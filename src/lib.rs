use scrypto::prelude::*;

#[derive(ScryptoSbor, NonFungibleData)]
pub struct YieldTokenData {
    underlying_lsu_resource: ResourceAddress,
    underlying_lsu_amount: Decimal,
    redemption_value_at_start: Decimal,
    yield_claimed: Decimal,
    maturity_date: UtcDateTime,
}

#[derive(ScryptoSbor, Clone)]
pub struct LSU {
    lsu_resource: ResourceAddress,
    lsu_amount: Decimal,
    maturity_date: UtcDateTime,
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
        lsu_vaults: HashMap<ResourceAddress, Vault>,
        lsu: Vec<LSU>,
        expiry_days: i64,
    }

    impl YieldStripping {
        pub fn instantiate_yield_stripping(
            expiry_days: i64,
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
                    minter => rule!(allow_all);
                    // minter => rule!(require(global_caller(component_address)));
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

            (Self {
                sxrd_rm,
                yt_rm,
                xrd_vault: FungibleVault::new(XRD),
                fee_vault: FungibleVault::new(sxrd_rm.address()),
                stripping_fee,
                yt_fee,
                lsu_vaults: HashMap::new(),
                lsu: Vec::new(),
                expiry_days,
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

        /// Check if some LSU can be unstaked.
        pub fn check_unstake(&mut self) -> Vec<Bucket> {
            let (lsu_mature, lsu_immature): (Vec<_>, Vec<_>) = self.lsu
                .iter()
                // Check if the maturity date of the LSU has been reached
                .partition(|lsu| Self::check_maturity(lsu.maturity_date));

            let unstaked_lsu = lsu_mature
                .into_iter()
                .map(|lsu| {
                    let mut lsu_validator_component = Self::retrieve_validator_component(
                        lsu.lsu_resource
                    );
                    let lsu_vault = self.lsu_vaults.get_mut(&lsu.lsu_resource).unwrap();
                    let required_lsu_bucket = lsu_vault.take(lsu.lsu_amount);
                    lsu_validator_component.unstake(required_lsu_bucket.into())
                })
                .collect::<Vec<Bucket>>();

            self.lsu = lsu_immature
                .into_iter()
                .map(|lsu| lsu.clone())
                .collect::<Vec<_>>();

            unstaked_lsu
        }

        /// Tokenizes the LSU to its PT and YT.
        ///
        /// # Arguments
        ///
        /// * `lsu_token`: [`FungibleBucket`] - A fungible bucket of LSU tokens to tokenize.
        ///
        /// # Returns
        ///
        /// * [`FungibleBucket`] - A fungible bucket of PT.
        /// * [`NonFungibleBucket`] - A non fungible bucket of YT.
        pub fn tokenize_yield(
            &mut self,
            lsu_token: FungibleBucket
        ) -> (FungibleBucket, NonFungibleBucket) {
            //assert_ne!(self.check_maturity(), true, "The expiry date has passed!");
            //assert_eq!(lsu_token.resource_address(), self.lsu_address);
            let lsu_address = lsu_token.resource_address();
            let lsu_validator_component = Self::retrieve_validator_component(lsu_address);
            assert_eq!(Self::validate_lsu(lsu_address), true, "Not an LSU!");

            let lsu_address = lsu_token.resource_address();
            let lsu_amount = lsu_token.amount();
            let redemption_value = lsu_validator_component.get_redemption_value(lsu_token.amount());

            let mut sxrd_bucket = self.sxrd_rm.mint(lsu_amount).as_fungible();

            self.fee_vault.put(sxrd_bucket.take(lsu_amount * self.stripping_fee));

            let yt_bucket = self.yt_rm
                .mint_ruid_non_fungible(YieldTokenData {
                    underlying_lsu_resource: lsu_address,
                    underlying_lsu_amount: lsu_amount,
                    redemption_value_at_start: redemption_value,
                    yield_claimed: Decimal::ZERO,
                    maturity_date: self.expiry_date(),
                })
                .as_non_fungible();

            // self.lsu_vault.put(lsu_token);
            if let Some(vault) = self.lsu_vaults.get_mut(&lsu_token.resource_address()) {
                vault.put(lsu_token.into());
            } else {
                self.lsu_vaults.insert(
                    lsu_token.resource_address(),
                    Vault::with_bucket(lsu_token.into())
                );
            }

            self.lsu.push(LSU {
                lsu_resource: lsu_address,
                lsu_amount,
                maturity_date: self.expiry_date(),
            });

            //return (pt_bucket, yt_bucket);
            return (sxrd_bucket, yt_bucket);
        }

        /// Claims owed yield for the period.
        ///
        /// # Arguments
        ///
        /// * `yt_proof`: [`NonFungibleProof`] - A non fungible proof of YT.
        ///
        /// # Returns
        ///
        /// * [`Bucket`] - A bucket of the Unstake NFT.
        /// Note: https://docs.radixdlt.com/docs/validator#unstake-nft
        pub fn claim_yield(&mut self, yt_proof: NonFungibleProof) -> Bucket {
            // Can no longer claim yield after maturity.
            // [TO CHECK]
            //assert_ne!(self.check_maturity(), true, "The yield token has reached its maturity!");

            let checked_proof = yt_proof.check(self.yt_rm.address());
            let mut data: YieldTokenData = checked_proof.non_fungible().data();

            // Calc yield owed (redemption value) based on difference of current redemption
            // value and redemption value at start.
            let yield_owed = self.calc_yield_owed(&data);

            let mut lsu_validator_component = Self::retrieve_validator_component(
                data.underlying_lsu_resource
            );
            // Calc amount of LSU to redeem to achieve yield owed.
            let required_lsu_for_yield_owed = self.calc_required_lsu_for_yield_owed(
                yield_owed,
                lsu_validator_component
            );

            // Burn the yield token by the amount of LSU required to redeem.
            data.underlying_lsu_amount -= required_lsu_for_yield_owed;
            data.yield_claimed += yield_owed;

            // LSU amount decreases but redemption value is the same
            let lsu_vault = self.lsu_vaults.get_mut(&data.underlying_lsu_resource).unwrap();
            let required_lsu_bucket = lsu_vault.take(required_lsu_for_yield_owed);

            lsu_validator_component.unstake(required_lsu_bucket.into())
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
            let lsu_validator_component = Self::retrieve_validator_component(
                data.underlying_lsu_resource
            );
            let redemption_value = lsu_validator_component.get_redemption_value(
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
        fn calc_required_lsu_for_yield_owed(
            &self,
            yield_owed: Decimal,
            lsu_validator_component: Global<Validator>
        ) -> Decimal {
            let total_xrd_staked = lsu_validator_component.total_stake_xrd_amount();
            let total_lsu_supply = lsu_validator_component.total_stake_unit_supply();

            total_xrd_staked
                .checked_div(total_lsu_supply)
                .and_then(|result| yield_owed.checked_mul(result))
                .unwrap()
        }

        /// Retrieves the `ResourceAddress` of sXRD.
        ///
        /// # Returns
        ///
        /// * [`ResourceAddress`] - The address of sXRD.
        pub fn pt_address(&self) -> ResourceAddress {
            self.sxrd_rm.address()
        }

        /// Retrieves the `ResourceAddress` of YT.
        ///
        /// # Returns
        ///
        /// * [`ResourceAddress`] - The address of YT.
        pub fn yt_address(&self) -> ResourceAddress {
            self.yt_rm.address()
        }

        /// Checks whether maturity date has been reached.
        /// Retuens true if cureent time >= maturity date.
        pub fn check_maturity(maturity_date: UtcDateTime) -> bool {
            Clock::current_time_comparison(
                maturity_date.to_instant(),
                TimePrecision::Second,
                TimeComparisonOperator::Gte
            )
        }

        /// Returns the expiry date.
        pub fn expiry_date(&self) -> UtcDateTime {
            let current_time = Clock::current_time_rounded_to_seconds();
            UtcDateTime::from_instant(&current_time.add_days(self.expiry_days).unwrap())
                .ok()
                .unwrap()
        }
    }
}
