// This blueprints implement a single asset staking pool based on the Liquity stability pool concept: https://www.liquity.org/blog/scaling-liquitys-stability-pool.
// The scaling feature described in the blog post is not implemented in this blueprint, we chose to use PreciseDecimal to mitigate the scaling issue of the running product.

// Ensuring 1:1 peg of sXRD to XRD peg required hard peg mechanism: sXRD need to be redeem with XRD at any time. in case the system lake XRD , sXRD will reddem for LSU and redeemed sXRD will be shared to the LSU provider.
// The purpose of this staking pool is to allow fair distribution of sXRD to LSU contributor.

use scrypto::prelude::*;

/// Data structure storing the state of contributor deposit snapshot
/// Info stored in this struct is used to calculate the amount of redeemable compounded deposit and gains
///
#[derive(ScryptoSbor, Clone, Debug)]
pub struct DepositSnapshot {
    /// The amount of deposit at the time of snapshot
    ///
    pub deposit_amount: Decimal,

    /// Snapshot of the epoch at the time of snapshot
    ///
    pub epoch: u8,

    /// Snapshot of running product at the time of snapshot
    ///
    pub running_sum: PreciseDecimal,

    /// Snapshot of running product at the time of snapshot
    ///
    pub running_product: PreciseDecimal,
}

#[blueprint]
#[types(NonFungibleLocalId, u8, PreciseDecimal, DepositSnapshot, Decimal)]
mod staking_pool {

    struct StakingPool {
        /// The address of the pool
        pool_res_address: ResourceAddress,

        /// Vault  used to store the deposit of the contributors.
        deposits: Vault,

        /// Vault storing gain distributed to the contributors.
        distributed_resources: Vault,

        /// Each time the pool is emptied, a new epoch is created by incrementing the epoch field.
        current_epoch: u8,

        /// The running sum of each epoch.
        running_sum: KeyValueStore<u8, PreciseDecimal>,

        /// The running product: the product of the consecutive inflation or depletion on deposit and withdraw.
        running_product: PreciseDecimal,

        /// This variable is use to track number of contribution to the pool.
        contribution_counter: u64,

        /// This variable is use to track the total amount of redemption from the pool.
        /// in conjunction with the contribution_counter, it is use to track the emptying of the pool.
        /// - if redemption_counter == contribution_counter, the pool is empty.
        /// - if contribution_counter - redemption_counter == 1, last contributor is interacting with the pool.
        redemption_counter: u64,

        /// The Product-Sum algorithm used to calculate the reward of the contributors is based on snapshots of some variables: the running product, the running sum, the epoch and the scale.
        /// Each time a contribution or a redemption is made, a snapshot of the 3 variables is taken and store in the `snapshots` variable.
        /// We also keep the value of the initial deposit amount in the snapshot to be able to calculate the reward of the contributor.
        snapshots: KeyValueStore<NonFungibleLocalId, DepositSnapshot>,

        /// The design of the system make each redemption complete, meaning that it will withdraw all claimable gain and contributor's compounded deposit.
        /// We introduce the `redeemed_gains` variable to keep the gains of the contributor for the next an internal redeem performed to allow partial stake or unstake.
        /// if the contributor want only to change the size of the deposit, he can do so and the system will keep the gains for the next claim.
        redeemed_gains: KeyValueStore<NonFungibleLocalId, Decimal>,
    }

    impl StakingPool {
        /// Instantiate a new StakingEngine
        ///
        /// # Arguments
        /// * `pool_mode` - The mode of the staking engine, either a resource or a decimal value.
        /// * `config` - The config of the staking engine.
        ///
        /// # Returns
        /// * The instantiated `StakingEngine` object.
        ///
        pub fn instantiate(
            pool_res_address: ResourceAddress,
            distributed_res_address: ResourceAddress,
        ) -> Owned<StakingPool> {
            Self {
                pool_res_address,
                current_epoch: 0,
                running_product: PreciseDecimal::ONE,
                contribution_counter: 0,
                redemption_counter: 0,
                deposits: Vault::new(pool_res_address),
                running_sum: KeyValueStore::new_with_registered_type(),
                snapshots: KeyValueStore::new_with_registered_type(),
                distributed_resources: Vault::new(distributed_res_address),
                redeemed_gains: KeyValueStore::new_with_registered_type(),
            }
            .instantiate()
        }

        /// * Pool management methods * ///

        /// Deposit assets in the pool
        /// This method is use to "inflate" the pool with compound effect on future rewards.
        /// The method call update the running product of the pool.
        ///
        /// # Arguments
        /// * `deposit: Bucket` - Bucket of assets added to the current pool deposits.
        ///
        pub fn deposit(&mut self, deposit: Bucket) {
            assert!(!self._is_pool_empty(), "EMPTY_POOL_DEPOSIT_ERROR");

            self._update_running_product(deposit.amount());

            self.deposits.put(deposit);
        }

        /// Withdraw assets from the pool
        /// This method is use to "deflate" the pool with compound effect on future rewards.
        /// The method call update the running product of the pool.
        ///
        /// # Arguments
        /// * `amount` - The amount to withdraw
        ///
        /// # Returns
        /// * `Bucket` - Asset withdrawn from the pool
        ///
        pub fn withdraw(&mut self, amount: Decimal) -> Bucket {
            assert!(amount > dec!(0), "WITHDRAW_NEGATIVE_AMOUNT_ERROR");

            assert!(!self._is_pool_empty(), "EMPTY_POOL_WITHDRAWAL_ERROR");

            let max_amount = self.deposits.amount().min(amount);

            self._update_running_product(-max_amount);

            self.deposits.take(max_amount)
        }

        /// Distribute gains to the contributors
        /// This method is use to distribute gains to the contributors. the gains are distributed based on the share of the contributor in the pool.
        /// If this method is call with the base asset of the pool, it will not be compounded. To have the compound effect, use the `deposit` method.
        ///
        /// # Arguments
        /// * `gain: Bucket` - The gains to distribute
        ///
        pub fn distribute(&mut self, gain: Bucket) {
            assert!(!self._is_pool_empty(), "EMPTY_POOL_DISTRIBUTION_ERROR");

            let deposits_amount = PreciseDecimal::from(self.deposits.amount());

            if self.running_sum.get_mut(&(self.current_epoch)).is_none() {
                self.running_sum
                    .insert(self.current_epoch, PreciseDecimal::ZERO);
            };

            let mut running_sum = self
                .running_sum
                .get_mut(&(self.current_epoch))
                .expect("MISSING_EPOCH_RUNNING");

            let gain_amount = PreciseDecimal::from(gain.amount());

            *running_sum += gain_amount * (self.running_product / deposits_amount);

            self.distributed_resources.put(gain);
        }

        /// * Pool contributors methods * ///

        /// Add a new contribution to a contributor id.
        /// If the contributor already have a contribution, the method will redeem the previous contribution and gain.
        /// Then it will add redeemed contribution to the new contribution.
        /// Gains will be stored for the next claim.
        ///
        /// # Arguments
        /// * `id` - The id of the contributor
        /// * `deposit` - The contribution to add to the pool
        ///
        pub fn contribute(&mut self, id: NonFungibleLocalId, deposit: Bucket) {
            let (compounded_deposit, _) = self._redeem_internal(&id);

            let stake_variation = deposit.amount();

            self.deposits.put(deposit);

            let total_stake = compounded_deposit + stake_variation;

            self._contribute_internal(id.clone(), total_stake);
        }

        /// Redeem the compounded deposit of a contributor id.
        /// Internally, the method will redeem the compounded deposit and gains of the contributor.
        /// Then it will keep gains in cache for the next claim.
        ///
        /// # Arguments
        /// * `id` - The id of the contributor
        /// * `amount` - The amount to redeem. If the amount is not provided, the method will redeem all the compounded deposit.
        ///
        /// # Returns
        /// * `Bucket` - The compounded deposit of the contributor.
        ///
        pub fn redeem(&mut self, id: NonFungibleLocalId, amount: Option<Decimal>) -> Bucket {
            let (compounded_deposit, _gain_amount) = self._redeem_internal(&id);

            let compounded_deposit =
                // if recent _redeem_internal emptied the pool
                if self.contribution_counter - self.redemption_counter == 0 {
                    self.deposits.amount()
                } else {
                    compounded_deposit
                };

            let redeem_amount = if let Some(amount) = amount {
                assert!(amount >= dec!(0), "INVALID_REDEEM_AMOUNT: {}", amount);
                self._contribute_internal(id.clone(), compounded_deposit - amount);
                amount
            } else {
                compounded_deposit
            };

            self.deposits.take(redeem_amount)
        }

        /// Claim gains of a contributor id. Internally, the method will claim the compounded deposit and gains of the contributor.
        /// Then it will contribute back the compounded deposit to the pool.
        ///
        /// # Arguments
        /// * `id` - The id of the contributor
        ///
        /// # Returns
        /// * `Bucket` - The gains of the contributor
        ///
        pub fn claim(&mut self, id: NonFungibleLocalId) -> Bucket {
            let (compounded_deposit, _) = self._redeem_internal(&id);

            // Remove stored redeemed gains amount (should never fail on unwrap as we just store it in _redeem_internal method)
            let gain_amount = self.redeemed_gains.remove(&id).unwrap();

            let (compounded_deposit, gain) =
                if self.contribution_counter - self.redemption_counter == 0 {
                    (
                        self.deposits.amount(),
                        self.distributed_resources.take_all(),
                    )
                } else {
                    (
                        compounded_deposit,
                        self.distributed_resources.take(gain_amount),
                    )
                };

            self._contribute_internal(id, compounded_deposit);

            gain
        }

        /// * Internal methods * ///

        /// Evaluate if the pool is empty.
        fn _is_pool_empty(&self) -> bool {
            self.contribution_counter == self.redemption_counter
                || self.deposits.amount() == dec!(0)
        }

        /// Internal method implementing core logic to contribute to the pool.
        /// Handle the case where the contributor already have a contribution.
        fn _contribute_internal(&mut self, id: NonFungibleLocalId, deposit_amount: Decimal) {
            assert!(
                self.snapshots.get(&id).is_none(),
                "CONTRIBUTION_OVERLAP_ERROR"
            );

            assert!(deposit_amount >= dec!(0), "CONTRIBUTION_NEGATIVE_AMOUNT");

            if deposit_amount == dec!(0) {
                return;
            }

            // If a snapshot does not exist for this id, create a new one.
            if self.running_sum.get(&(self.current_epoch)).is_none() {
                self.running_sum
                    .insert(self.current_epoch, PreciseDecimal::ZERO);
            }
            let running_sum = self.running_sum.get(&self.current_epoch).unwrap();

            self.snapshots.insert(
                id.clone(),
                DepositSnapshot {
                    deposit_amount,
                    epoch: self.current_epoch,
                    running_product: self.running_product,
                    running_sum: *running_sum,
                },
            );

            self.contribution_counter += 1;
        }

        /// Internal method implementing core logic to redeem a contribution from the pool.
        /// Handle the case where the contributor already have a contribution and redeemed gains.
        fn _redeem_internal(&mut self, id: &NonFungibleLocalId) -> (Decimal, Decimal) {
            let (compounded_deposit_amount, gain_amount) = self._get_redeemable_value(id);

            if self.snapshots.get(id).is_some() {
                self.redemption_counter += 1;

                self.snapshots.remove(id).expect("SNAPSHOT_NOT_FOUND_ERROR");

                self.redeemed_gains.insert(id.clone(), gain_amount);
            }

            (compounded_deposit_amount, gain_amount)
        }

        /// Internal method implementing core logic to update the running product of the pool.
        /// The method is called each time a deposit or a withdrawal is made.
        fn _update_running_product(&mut self, amount: Decimal) {
            let total_deposit_amount = self.deposits.amount();

            if total_deposit_amount == -amount || total_deposit_amount == dec!(0) {
                self.current_epoch += 1;
                self.running_product = PreciseDecimal::ONE;
            } else {
                self.running_product *=
                    PreciseDecimal::from(dec!(1) + (amount / self.deposits.amount()));
            }
        }

        fn _get_redeemable_value(&self, id: &NonFungibleLocalId) -> (Decimal, Decimal) {
            // load previous redeemed gains if any
            let mut redeemed_gain_amounts =
                if let Some(redeemed_gains) = self.redeemed_gains.get(id) {
                    *redeemed_gains
                } else {
                    Decimal::ZERO
                };

            let compounded_deposit_amount = if let Some(snapshot) = self.snapshots.get(id) {
                let epoch_running_sum = match self.running_sum.get(&(snapshot.epoch)) {
                    Some(running_sum) => *running_sum,
                    None => PreciseDecimal::ZERO,
                };

                // gain at each scale is adjusted with the scale factor
                let gain_amount = // process gain amount
                             (PreciseDecimal::from(snapshot.deposit_amount)
                                / snapshot.running_product)
                                * (epoch_running_sum - snapshot.running_sum)
                                    ;

                redeemed_gain_amounts += gain_amount
                    .checked_truncate(RoundingMode::ToNearestMidpointToEven)
                    .unwrap();
                // }

                // Calculate the compounded deposit amount using the processed running product at the scale of the snapshot.
                if snapshot.epoch == self.current_epoch {
                    PreciseDecimal::from(snapshot.deposit_amount) / snapshot.running_product
                } else {
                    PreciseDecimal::ZERO
                }
            } else {
                PreciseDecimal::ZERO
            };

            (
                compounded_deposit_amount
                    .checked_truncate(RoundingMode::ToNearestMidpointToEven)
                    .unwrap(),
                redeemed_gain_amounts,
            )
        }
    }
}
