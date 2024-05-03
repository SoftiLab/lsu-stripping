# **Yield Tokenizer** 


The Yield Tokenizer is a yield derivative protocol that offers the possibility to profit from the current XRD value of LSUs without losing the exposure to the yield they can generate in the future. To achieve this, the Yield Tokenizer dApp uses LSUs as input and generates two resources as output: a fungible resource, the **sXRD**, and a non-fungible one, the **Yield Token (YT)**. The sXRD is a synthetic derivative designed to have roughly the same market value as the XRD. The YT, on the other hand, represent current position in LSU and can be exchanged at any time for XRD whose value close to the yield generated by the LSUs that were used for its creation. The use of NFTs for representing yield positions allows for the support of multiple LSUs, but for the purpose of this challenge, we will consider that the LSUs come from the same validator. 

## Demo
 a POC dApp is available here : [Demo](https://lsu-yield-tokenizer.vercel.app)
 
## System Operation

To ensure these functions, the system is structured around 3 processes:

### Minting
Minting involves the creation of sXRD and a YT. It takes LSUs as input. The amount of sXRD created corresponds to the amount of XRD exchangeable with the deposited LSUs. The YT will record the amount of sXRD paid out and will serve as a receipt to represent the share of the deposited LSUs in the total amount of deposited LSUs (similar to a staking receipt). To facilitate arbitrage operations, Minting could also accept XRD deposited in the unstaking vault and create the corresponding sXRD (more details will be provided later).

![sXRD and YT minting](images/mint-sxrd-and-yt.png)

### sXRD Conversion

The sXRD presented to the system are exchanged for XRD at a 1:1 ratio. The returned XRD come from the Vault containing the XRD obtained during the YT conversion phase. If the pool does not contain enough XRD, the system will enter “forced” mode and will return a quantity of LSUs whose exchange value corresponds to the quantity of XRD to be returned. The forced mode is designed to guarantee sXRD/XRD convertibility and will involve sXRD penalty that will be distributed to the YT holders.

![sXRD redemption](images/redeem-sxrd.png)

### Yield Token Conversion

 The conversion of YT happens in two steps. The first step involves withdrawing the LSUs corresponding to the deposited YTs and initiating an unstake. The native unstake receipt is kept within the system. The system will modify the yield receipt to account for the ongoing unstake. The second step involves claiming the native receipt once the unstake waiting period has expired. An amount of XRD will be withheld from the unstake return; this quantity corresponds to the sXRD created during the Minting phase. The withheld XRD are stored in a vault that will serve for the rapid conversion of sXRD.

![Yield claim (sXRD or LSU)](images/redeem-yt.png)

### Fees 
Fees are can be levied on two occasions: At the creation of sXRD and during their conversion into XRD. The value of these fees defines a fluctuation range for the price of sXRD in XRD as they set the range around the price where arbitrage opportunities remain profitable. fees are not implemented in this submission but can easily be implemented.

## Interaction with the External System

The 1:1 convertibility with XRD of sXRD offers an opportunity for an external exchange pool between sXRD/XRD. This pool could even be subject to incentives, as it will participate in maintaining the value of sXRD at 1 XRD by offering direct arbitrage opportunities. Considering an arbitrager with an initial capital in XRD, we have the following scenarios:

If sXRD is more expensive than XRD at the external pool level, an arbitrager could deposit XRD in the Yield Tokenizer and systematically resell the obtained sXRD.

If XRD is more expensive than sXRD, the arbitrager could buy sXRD and convert them into XRD. In the situation of a lack of liquidity in XRD, they will obtain LSUs whose value will no longer depend on the value of sXRD but rather on the quantity of XRD exchangeable with these LSUs. 

## Potential added value:

The Yield Tokenizer presents an interest for two types of actors: liquidity providers and individuals looking to leverage their LSU position without compromising their exposure to the yield.

For liquidity providers, the Yield Tokenizer offers an attractive volume potential. By participating in the system as LSU providers, they can benefit from the creation of sXRD, a synthetic derivative with a market value similar to that of XRD. Moreover, the 1:1 convertibility with XRD guarantees a volume due to arbitrage activity.

For those looking to leverage their LSU position while maintaining their exposure to the yield, the Yield Tokenizer offers an attractive solution. By converting their LSUs into sXRD and receiving YTs, they can maintain part of their investment while freeing up capital for other opportunities.

## Risks

Although the Yield Tokenizer system offers attractive benefits, it also carries certain potential risks that must be considered:

Liquidity Risk: As with any financial system, the risk of a lack of liquidity is present. If the external exchange pool between sXRD and XRD is not sufficiently liquid, this could lead to difficulties in converting positions from sXRD to XRD or vice versa, which could affect users’ ability to carry out their transactions as needed.

Market Risk: Fluctuations in the price of XRD can affect the value of the created sXRD and the held YTs. If the price of XRD undergoes significant fluctuations, this could impact the value of the assets held in the Yield Tokenizer system, potentially leading to losses for investors.

However, these risks are mitigated by the fact that each sXRD in circulation corresponds to sealed LSUs or XRD.

