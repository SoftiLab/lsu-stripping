use scrypto::prelude::*;

#[derive(ScryptoSbor, NonFungibleData)]
pub struct YieldTokenData {
    underlying_lsu_resource: ResourceAddress,
    underlying_lsu_amount: Decimal,
    redemption_value_at_start: Decimal,
    yield_claimed: Decimal,
}

#[derive(ScryptoSbor, NonFungibleData)]
pub struct UnstakeData {
    pub name: String,
    pub claim_epoch: Epoch,
    pub claim_amount: Decimal,
}

#[blueprint]
mod yield_stripping {
    struct YieldStripping {
        sxrd_rm: ResourceManager,
        yt_rm: ResourceManager,

        xrd_vault: FungibleVault,
        fee_vault: FungibleVault,
        stripping_fee: Decimal,
        yt_fee: Decimal,
        lsu_validator_component: Global<Validator>,
        lsu_address: ResourceAddress,
        lsu_vault: FungibleVault,

        claim_vault: Option<NonFungibleVault>,
    }

    impl YieldStripping {
        pub fn instantiate_yield_stripping(
            accepted_lsu: ResourceAddress,

            stripping_fee: Decimal,
            yt_fee: Decimal
        ) -> Global<YieldStripping> {
            assert!(
                Decimal::ZERO <= stripping_fee && stripping_fee <= Decimal::ONE,
                "Stripping fee must be between zero and one!"
            );
            assert!(
                Decimal::ZERO <= yt_fee && yt_fee <= Decimal::ONE,
                "Yield token fee must be between zero and one!"
            );

            let (address_reservation, component_address) = Runtime::allocate_component_address(
                YieldStripping::blueprint_id()
            );

            // sXRD
            let sxrd_rm: ResourceManager = ResourceBuilder::new_fungible(OwnerRole::None)
                .divisibility(DIVISIBILITY_MAXIMUM)
                .metadata(
                    metadata! {
                    init {
                        "name" => "sXRD Token", locked;
                        "symbol" => "sXRD", locked;
                        "yield_tokenizer_component" => GlobalAddress::from(component_address), locked;
                    }
                }
                )
                .mint_roles(
                    mint_roles! {
                    minter => rule!(require(global_caller(component_address)));
                    minter_updater => rule!(deny_all);
                }
                )
                .burn_roles(
                    burn_roles! {
                    burner => rule!(require(global_caller(component_address)));
                    burner_updater => rule!(deny_all);
                }
                )
                .create_with_no_initial_supply();

            // YT
            let yt_rm: ResourceManager = ResourceBuilder::new_ruid_non_fungible::<YieldTokenData>(
                OwnerRole::None
            )
                .metadata(
                    metadata! {
                init {
                    "name" => "Yield Receipt", locked;
                    "symbol" => "YT", locked;
                    "yield_stripping_component" => GlobalAddress::from(component_address), locked;
                }
            }
                )
                .mint_roles(
                    mint_roles! {
                minter => rule!(require(global_caller(component_address)));
                minter_updater => rule!(deny_all);
            }
                )
                .burn_roles(
                    burn_roles! {
                burner => rule!(allow_all);
                burner_updater => rule!(deny_all);
            }
                )
                .non_fungible_data_update_roles(
                    non_fungible_data_update_roles! {
                non_fungible_data_updater => rule!(require(global_caller(component_address)));
                non_fungible_data_updater_updater => rule!(deny_all);
            }
                )
                .create_with_no_initial_supply();

            let lsu_validator_component = Self::retrieve_validator_component(accepted_lsu);
            assert_eq!(Self::validate_lsu(accepted_lsu), true, "Not an LSU!");

            (Self {
                sxrd_rm,
                yt_rm,
                xrd_vault: FungibleVault::new(XRD),
                fee_vault: FungibleVault::new(sxrd_rm.address()),
                stripping_fee,
                yt_fee,
                lsu_validator_component,
                lsu_address: accepted_lsu,
                lsu_vault: FungibleVault::new(accepted_lsu),

                claim_vault: None,
            })
                .instantiate()
                .prepare_to_globalize(OwnerRole::None)
                .with_address(address_reservation)
                .globalize()
        }

        /// Retrieve validator component.
        fn retrieve_validator_component(lsu_address: ResourceAddress) -> Global<Validator> {
            let metadata: GlobalAddress = ResourceManager::from(lsu_address)
                .get_metadata("validator")
                .unwrap()
                .unwrap_or_else(|| Runtime::panic(String::from("Not an LSU!")));
            ComponentAddress::try_from(metadata).unwrap().into()
        }

        /// Validate lsu.
        fn validate_lsu(input_lsu_address: ResourceAddress) -> bool {
            let metadata: GlobalAddress = ResourceManager::from(input_lsu_address)
                .get_metadata("validator")
                .unwrap()
                .unwrap_or_else(|| Runtime::panic(String::from("Not an LSU!")));
            let validator_address = ComponentAddress::try_from(metadata).unwrap();
            let validator: Global<Validator> = Global::from(validator_address);
            let lsu_address: GlobalAddress = validator
                .get_metadata("pool_unit")
                .unwrap()
                .unwrap_or_else(|| Runtime::panic(String::from("Not an LSU!")));

            input_lsu_address == ResourceAddress::try_from(lsu_address).unwrap()
        }

        /// Tokenizes the LSU to its sXRD and YT.
        ///
        /// # Arguments
        ///
        /// * `lsu_token`: [`FungibleBucket`] - A fungible bucket of LSU tokens to tokenize.
        ///
        /// # Returns
        ///
        /// * [`FungibleBucket`] - A fungible bucket of sXRD.
        /// * [`NonFungibleBucket`] - A non fungible bucket of YT.
        pub fn tokenize_yield(
            &mut self,
            lsu_token: FungibleBucket
        ) -> (FungibleBucket, NonFungibleBucket) {
            assert_eq!(lsu_token.resource_address(), self.lsu_address);

            let lsu_amount = lsu_token.amount();
            let redemption_value = self.lsu_validator_component.get_redemption_value(
                lsu_token.amount()
            );

            let mut sxrd_bucket = self.sxrd_rm.mint(lsu_amount).as_fungible();

            self.fee_vault.put(sxrd_bucket.take(lsu_amount * self.stripping_fee));

            let yt_bucket = self.yt_rm
                .mint_ruid_non_fungible(YieldTokenData {
                    underlying_lsu_resource: self.lsu_address,
                    underlying_lsu_amount: lsu_amount,
                    redemption_value_at_start: redemption_value,
                    yield_claimed: Decimal::ZERO,
                })
                .as_non_fungible();

            self.lsu_vault.put(lsu_token);

            return (sxrd_bucket, yt_bucket);
        }

        /// Mint sXRD with XRD.
        pub fn mint_sxrd(&mut self, xrd_token: FungibleBucket) -> FungibleBucket {
            assert_eq!(xrd_token.resource_address(), XRD);
            let xrd_amount = xrd_token.amount();
            self.xrd_vault.put(xrd_token);
            self.sxrd_rm.mint(xrd_amount).as_fungible()
        }

        /// Redeem sXRD for XRD.
        pub fn redeem_sxrd_for_xrd(&mut self, sxrd_bucket: FungibleBucket) -> FungibleBucket {
            assert_eq!(sxrd_bucket.resource_address(), self.sxrd_rm.address());
            // TODO: Give LSU if not enough XRD
            assert!(sxrd_bucket.amount() <= self.xrd_vault.amount(), "Not enough XRD!");

            let xrd_bucket = self.xrd_vault.take(sxrd_bucket.amount());
            sxrd_bucket.burn();
            xrd_bucket
        }

        /// Redeem sXRD for LSU.
        pub fn redeem_sxrd_for_lsu(&mut self, sxrd_bucket: FungibleBucket) -> FungibleBucket {
            assert_eq!(sxrd_bucket.resource_address(), self.sxrd_rm.address());
            // Calc amount of LSU to redeem to achieve yield owed.
            let required_lsu_for_sxrd = self.calc_required_lsu_for_yield_owed(sxrd_bucket.amount());
            let lsu_bucket = self.lsu_vault.take(required_lsu_for_sxrd);
            sxrd_bucket.burn();
            lsu_bucket
        }

        /// Unstake LSU and put in LSU Vault
        fn unstake_lsu(&mut self, lsu_bucket: Bucket) {
            let unstake_bucket = self.lsu_validator_component.unstake(lsu_bucket);
            match self.claim_vault {
                None => {
                    self.claim_vault = Some(
                        NonFungibleVault::with_bucket(unstake_bucket.as_non_fungible())
                    );
                }
                Some(ref mut vault) => vault.put(unstake_bucket.as_non_fungible()),
            };
        }

        /// Claim NFTs and put in XRD Vault
        pub fn claim_nfts(&mut self, limit: u32) {
            if let Some(ref mut vault) = self.claim_vault {
                let claimable_nft_ids = vault
                    .non_fungible_local_ids(limit)
                    .into_iter()
                    .filter(|id| {
                        let resource_manager = vault.resource_manager();
                        let data = resource_manager.get_non_fungible_data::<UnstakeData>(&id);

                        Runtime::current_epoch() <= data.claim_epoch
                    })
                    .collect::<IndexSet<NonFungibleLocalId>>();

                if claimable_nft_ids.len() != 0 {
                    let claimable_bucket = vault.take_non_fungibles(&claimable_nft_ids);

                    let xrd_bucket: Bucket = self.lsu_validator_component.claim_xrd(
                        claimable_bucket.into()
                    );
                    self.xrd_vault.put(xrd_bucket.as_fungible());
                }
            }
        }

        /// Claims owed yield for LSU.
        pub fn claim_yield_for_lsu(&mut self, yt_proof: NonFungibleProof, lsu_amount:Option<Decimal>) -> FungibleBucket {
            let checked_proof = yt_proof.check(self.yt_rm.address());
            let mut data: YieldTokenData = checked_proof.non_fungible().data();

            let yield_owed = self.calc_yield_owed(&data);

            let (lsu_to_unstake,yield_owed) = match lsu_amount {
                Some(lsu_amount) => (lsu_amount,yield_owed.checked_div(data.underlying_lsu_amount).unwrap())
                None => (data.underlying_lsu_amount,yield_owed)
            }

            let required_lsu_for_yield_owed = self.calc_required_lsu_for_yield_owed(yield_owed);

            data.underlying_lsu_amount -= lsu_to_unstake;
            data.yield_claimed += yield_owed;

            let required_lsu_bucket = self.lsu_vault.take(required_lsu_for_yield_owed);

            // Unstake underlying lsu amount.
            let lsu_bucket = self.lsu_vault.take(lsu_to_unstake).into();
            self.unstake_lsu(lsu_bucket);

            required_lsu_bucket
        }

        /// Claims owed yield for sXRD.
        pub fn claim_yield_for_sxrd(&mut self, yt_proof: NonFungibleProof) -> FungibleBucket {
            let checked_proof = yt_proof.check(self.yt_rm.address());
            let mut data: YieldTokenData = checked_proof.non_fungible().data();

            let yield_owed = self.calc_yield_owed(&data);

         
            // Unstake underlying lsu amount.
            let lsu_bucket = self.lsu_vault.take(data.underlying_lsu_amount).into();
            self.unstake_lsu(lsu_bucket);

            let required_lsu_for_yield_owed = self.calc_required_lsu_for_yield_owed(yield_owed);

            data.underlying_lsu_amount -= required_lsu_for_yield_owed;
            data.yield_claimed += yield_owed;

            let sxrd_value = self.lsu_validator_component.get_redemption_value(yield_owed);
            self.sxrd_rm.mint(sxrd_value).as_fungible()
        }

        /// Calculates earned yield of YT.
        ///
        /// # Arguments
        ///
        /// * `data`: [`&YieldTokenData`] - The `NonFungibleData` of YT.
        ///
        /// # Returns
        ///
        /// * [`Decimal`] - The calculated earned yield from YT for the current period.
        fn calc_yield_owed(&self, data: &YieldTokenData) -> Decimal {

            let redemption_value = self.lsu_validator_component.get_redemption_value(
                data.underlying_lsu_amount
            );

            info!("Redemption Value: {:?}", redemption_value);

            let redemption_value_at_start = data.redemption_value_at_start;

            info!("Redemption Value: {:?}", redemption_value_at_start);

            assert!(redemption_value > redemption_value_at_start, "No rewards earned yet.");

            redemption_value.checked_sub(redemption_value_at_start).unwrap()
        }

        /// Calculates the required LSU to redeem yield earned for the period.
        ///
        /// # Arguments
        ///
        /// * `yield_owed`: [`Decimal`] - The redemption value of the yield owed.
        ///
        /// # Returns
        ///
        /// * [`Decimal`] - The required LSU amount to redeem yield owed.
        fn calc_required_lsu_for_yield_owed(&self, yield_owed: Decimal) -> Decimal {

            let one_lsu_redemption_value = self.lsu_validator_component.lsu_validator_component(
               Decimal::ONE;
            );

            yield_owed.checked_div(one_lsu_redemption_value).unwrap()


            // let total_xrd_staked = self.lsu_validator_component.total_stake_xrd_amount();
            // let total_lsu_supply = self.lsu_validator_component.total_stake_unit_supply();

            // total_xrd_staked
            //     .checked_div(total_lsu_supply)
            //     .and_then(|result| yield_owed.checked_mul(result))
            //     .unwrap()
        }

        /// Retrieves the `ResourceAddress` of sXRD.
        ///
        /// # Returns
        ///
        /// * [`ResourceAddress`] - The address of sXRD.
        fn sxrd_address(&self) -> ResourceAddress {
            self.sxrd_rm.address()
        }

        /// Retrieves the `ResourceAddress` of YT.
        ///
        /// # Returns
        ///
        /// * [`ResourceAddress`] - The address of YT.
        fn yt_address(&self) -> ResourceAddress {
            self.yt_rm.address()
        }

        /// Retrieves the `ResourceAddress` of the underlying LSU.
        ///
        /// # Returns
        ///
        /// * [`ResourceAddress`] - The address of the underlying LSU.
        fn underlying_resource(&self) -> ResourceAddress {
            self.lsu_address
        }
    }
}
