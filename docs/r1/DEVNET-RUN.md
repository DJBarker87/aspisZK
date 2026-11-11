# The devnet runs

The current version of Aspis has run on Solana devnet three times. The most
recent run, on 11 November 2026, is the one to look at first. It settled a
private transfer and a private withdrawal and then closed each payment's
accounts, which returned the rent deposited for them. The run of 10 November
2026 was the first in which the frozen pool and a verifier built from the
frozen source ran together as deployed programs. An earlier run on 29 October
2026 settled the same two spends with the release verifier and an older build
of the pool. All three are described below, with links to the transactions on
the devnet explorer.

In every run a spend takes two transactions. The first runs the opening stage
of the verifier and writes a checkpoint account. The second resumes from that
checkpoint, completes verification and settles the payment in the pool. In the
two November runs the second transaction is a pool instruction, which is why
the tables below list it under the pool.

## The run of 11 November

This run used a new build of the verifier and a new, small upload program.
The verifier's public statement is longer than before, and the verifier has
an added instruction that closes a payment's checkpoint account. The upload
program holds the proof and the statement while they are written to the chain
and closes those accounts afterwards. Closing returns the rent that was
deposited to create the accounts, which the earlier runs left behind. The
pool program is the one deployed on 10 November, with fresh state.

| Program | Address | ELF SHA-256 | Upgradeability |
| --- | --- | --- | --- |
| Pool, unchanged | [`37hdATMk…Db3Zt`](https://explorer.solana.com/address/37hdATMkskKX1hiCWhz4nnzkD7GauYwX8EQwcpUDb3Zt?cluster=devnet) | `e0e49c34…09dc` | as on 10 November |
| Verifier | [`BLgzrkDi…X3xNg`](https://explorer.solana.com/address/BLgzrkDiCs4f7bwWrP4EBSNN5nhi2snfoLopxs2X3xNg?cluster=devnet) | `2284239e…`, 1,567,992 bytes | immutable, deployed at slot 520961115 |
| Upload program | [`9DYn3ykk…WqX5`](https://explorer.solana.com/address/9DYn3ykkW6JEgYVKst7y7Jd9SqxSjoSNUVTgnGCHWqx5?cluster=devnet) | `9b2ab3d4…`, 25,992 bytes | immutable, deployed at slot 520961219 |

Both new programs were rebuilt twice from the pinned source, commit
`c7593d23fdc`, in fresh build directories, and each rebuild gave the same
bytes. Before the run a check confirmed that the bytes on chain equal those
files and that both programs are immutable.

The run initialised a fresh pool, made two deposits and a forest checkpoint,
and then settled one transfer and one withdrawal. As before, it submitted each
settlement a second time and submitted each spend once more with the stage-1
proof altered. At the end of each payment it closed the payment's accounts.

| Step | Program | Compute units | Result | Transaction |
| --- | --- | ---: | --- | --- |
| Pool initialisation | Pool | 136,374 | ok | [`2jcFrD…gKmLF`](https://explorer.solana.com/tx/2jcFrDT31UyLavzmeheLjicowt2ZYXb13Pp33wyKVg7z4ZuVg75h8F7N4XmenaaxWo1qae1DhggjNfHqAmPgKmLF?cluster=devnet) |
| Deposit 0 | Pool | 1,111,471 | ok | [`5pZ3LK…zTs5r`](https://explorer.solana.com/tx/5pZ3LK3dndNYNhRv9VtcLdR5oE4kMiQZytxDutuzfZkoQNktSwyyfo8NZQZu8T2iDogMykZwRMiUjQCoNPBzTs5r?cluster=devnet) |
| Deposit 1 | Pool | 1,108,466 | ok | [`5xKYLU…QDCoz`](https://explorer.solana.com/tx/5xKYLUCCG7cNkwy9iDYxQLFXGFbiZax7dK5r13BQpTKx1yS1eDgLvzoHGijTu8Va44pmo8Qwgz9p37C5dXZQDCoz?cluster=devnet) |
| Forest checkpoint | Pool | 1,153,927 | ok | [`3L2Vrz…9z28d`](https://explorer.solana.com/tx/3L2Vrz4Zqu5hujRE3tVrVLx2RNmsYfTLhb9F74VzM44CBvg1FSxc2Tb3sSVxC45kGXYS32cJMeykRBAuxww9z28d?cluster=devnet) |
| Transfer, stage 1 | Verifier | 1,211,658 | ok, slot 520963484 | [`57k7sc…MkZ2R`](https://explorer.solana.com/tx/57k7scVRsChfDvppGoj9UmX83BbUHmRm7jc7yVEwejJfipzJzcX4xBimouxk4kdfRKeHeUzSSXJKzxS62wjMkZ2R?cluster=devnet) |
| Transfer, stage 2 and settlement | Pool | 1,139,928 | ok, slot 520963524 | [`4QKVyJ…SEXKa`](https://explorer.solana.com/tx/4QKVyJYbyhmtN4EpPNnGukfrmF7dFyFWzgrXz12yxaHaptaJg6YV8oUJW2Gt6dLpYS2eo7tPgaAqB7rJpzsSEXKa?cluster=devnet) |
| Replay of the transfer's settlement | Pool | 67,240 | rejected, NullifierAlreadyConsumed | [`2JkeX3…NEt1j`](https://explorer.solana.com/tx/2JkeX314uKnQmNU6rVi4EVzJ1haJWyUjo6MzsM1bwP5hG9vfgFFcKqWsrpE5JQn4nChimqtVsouLpEmBzdCNEt1j?cluster=devnet) |
| Transfer with a mutated stage-1 proof | Verifier | 21,453 | rejected, InvalidInstructionData | [`43rdvs…H74L5`](https://explorer.solana.com/tx/43rdvsL4qfX5RvLwWvNbywi6L7D54j28jGh1vdCDvpbtGTq3jyiKPXADfHaH4fww1uUpHTaJAdJBwEhuV6nH74L5?cluster=devnet) |
| Transfer, closing the accounts | Upload and verifier | 3,826 | ok | [`52nnJH…MwkNd`](https://explorer.solana.com/tx/52nnJHcFMNHLm3QvLYvVTgJuC1BhBXKgFFWoJjcfF4b8wYEGFmjXzCA3oar4Lt47eA6gg7Jz1UXR2K3YBi6MwkNd?cluster=devnet) |
| Withdrawal, stage 1 | Verifier | 1,205,338 | ok, slot 520964903 | [`2AGG8Q…xMUsL`](https://explorer.solana.com/tx/2AGG8QQVaBVHJN8H1gvhKKzPATcPbRYHvELnRpztVYXCVnMSWNS1qyNWu4mPT5F9n6NFPEn9dYqeET5JMEZxMUsL?cluster=devnet) |
| Withdrawal, stage 2 and settlement | Pool | 1,155,486 | ok, slot 520964933 | [`4pQ2aW…6qqm1`](https://explorer.solana.com/tx/4pQ2aWTwHoS96Q1pUDSFfuQKF8rQBvMmkzUsWNhhF42DUMK7HtL4238EwyEQQJusm6HJp6S9x2R3JasRd2T6qqm1?cluster=devnet) |
| Replay of the withdrawal's settlement | Pool | 68,841 | rejected, NullifierAlreadyConsumed | [`ayg7BL…kBYgv`](https://explorer.solana.com/tx/ayg7BLroykUdTdpxz6izXthcDugbpAhrzQEZwAZ8ReQc2p8gVVBa9xoj5tfCFGpbr4ZUV1fiv9CGx654GNkBYgv?cluster=devnet) |
| Withdrawal with a mutated stage-1 proof | Verifier | 21,395 | rejected, InvalidInstructionData | [`34zpkF…RPoys`](https://explorer.solana.com/tx/34zpkFpHfNatpaaLZ6LVjxrE4bNsuYLivx5PTFhEmCfpoM47t9P1q9fZFHtkL5fPbzbZ2XRe5AU5zh8bCS1RPoys?cluster=devnet) |
| Withdrawal, closing the accounts | Upload and verifier | 3,826 | ok | [`2dqZzT…VWMye`](https://explorer.solana.com/tx/2dqZzTq4YCmB9wcG25GNEG3xnucTb5mhPTj8Wb5vmQQGcBf2guLwXEjezZdJqjHxHGoApyJpCotjMkv7eDJVWMye?cluster=devnet) |

Both spends settled, both replays were rejected because the nullifier had
already been consumed, and both altered proofs were rejected by the first
stage. The run was 73 transactions in all, counting the setup, the uploads
and the tests, and every one was finalized.

### What a payment costs

A payment on its own takes 23 transactions. Two create the proof and
statement accounts, seventeen upload the data, one creates the checkpoint,
two verify and settle, and one closes the accounts.

| | Lamports | SOL |
| --- | ---: | ---: |
| Rent deposited for the proof, statement and checkpoint accounts | 316,621,160 | 0.3166 |
| Rent returned by the closing transaction | 316,621,160 | 0.3166 |
| Transaction fees for the 23 transactions | 345,000 | 0.0003 |
| Rent for the record of the spent nullifier, which stays | 1,706,880 | 0.0017 |
| Net cost to the payer | 2,051,880 | 0.0021 |

The figures were the same for the transfer and the withdrawal, and the
payer's balance before and after the run agrees with them. The record of the
spent nullifier is what prevents a note from being spent twice, so its rent is
never returned.

## The run of 10 November

The pool program used in October cannot be upgraded, because its upgrade
authority key was lost, and the release verifier has that pool's address
compiled in. For this run the frozen pool was therefore deployed at a new
address, and the verifier was rebuilt from the frozen source with only the
pool address changed.

| Program | Address | ELF SHA-256 | Upgradeability |
| --- | --- | --- | --- |
| Pool, frozen source | [`37hdATMk…Db3Zt`](https://explorer.solana.com/address/37hdATMkskKX1hiCWhz4nnzkD7GauYwX8EQwcpUDb3Zt?cluster=devnet) | `e0e49c344d35575116c0359450315ea4334bfb03006551727f67c04a8cfe09dc` | upgradeable, authority held by the deployment payer |
| Verifier, frozen source with the new pool address | [`GqZzWuGT…nr5hy`](https://explorer.solana.com/address/GqZzWuGTojfsxYnDzmyWKhdPGkce19xN1Txu9Vgnr5hy?cluster=devnet) | `2331ad8a2d97439a30329328c51f619a6b13be97e260ab1e1fd8aab22cb996ea` | immutable since slot 520604638 |

The verifier ELF differs from the release verifier ELF of October in 31 bytes,
all inside the 32-byte slot that holds the pool address, and so it is a new
build of the frozen verifier source and is distinct from the release pin. The
rebuild was reproduced twice, and a control build with the original address
reproduced the release pin exactly on the same day. How to repeat these builds
is in [`BUILD.md`](BUILD.md).

The run initialised a fresh pool, made two deposits and a forest checkpoint,
and then settled one transfer and one withdrawal. After each settlement it
submitted the same settlement again, and it submitted each spend once more
with the stage-1 proof altered.

| Step | Program | Compute units | Result | Transaction |
| --- | --- | ---: | --- | --- |
| Pool initialisation | Pool | 124,374 | ok | [`65nDh6…W2pK3`](https://explorer.solana.com/tx/65nDh6VGuyG71NwSRcANcczGqbZiXXhuYUe9E4JggQKB5SCr4pK4rYSaK2FwMyzRc2ZV49JPxyFpiYk3hCaW2pK3?cluster=devnet) |
| Deposit 0 | Pool | 1,106,971 | ok | [`37ev7k…xaomR`](https://explorer.solana.com/tx/37ev7k57r8okb1BhsXBFH6yNonn3TsMbBkADRYkL95o2hSdVqAKmhsNcZxeCg4RrxHg6zqd1YQayjKS5thxxaomR?cluster=devnet) |
| Deposit 1 | Pool | 1,106,966 | ok | [`2HDZhF…QXmCZ`](https://explorer.solana.com/tx/2HDZhFXWxWzR9kVrfBPffCFd11EbztaoVHYhFWBXfvEp6v5hAHcEv8YG9Wg3xoSoxo6KA7vEbagFpuJz396QXmCZ?cluster=devnet) |
| Forest checkpoint | Pool | 1,153,927 | ok | [`3GLEzr…Q6c4F`](https://explorer.solana.com/tx/3GLEzr5YXQX24KhTJwrNRbt1B22XfmJPzG7u7hheU2aKYwgECbUvrSfk9URjshAbvsxt3F3j2DHbGnLysWkQ6c4F?cluster=devnet) |
| Transfer, stage 1 | Verifier | 1,208,613 | ok, slot 520606640 | [`pUEwuh…Hz4i8`](https://explorer.solana.com/tx/pUEwuhuSNmr8PK159eVxZhwJGHAceLr8qLLcE4b3gdJ3qTuFz9NgoGXwhe6VrL646VhRj6AzmSXuyuQTq8Hz4i8?cluster=devnet) |
| Transfer, stage 2 and settlement | Pool | 1,138,552 | ok, slot 520606678 | [`5bPwiK…UBmCt`](https://explorer.solana.com/tx/5bPwiKGmcXgRQnEJfbUrxHU1kuQgu3Q4GMrZ8V76jCHTxmqr3zVKkjcsk5JNmP9PXtimkrQBzvf5SQ4Chq4UBmCt?cluster=devnet) |
| Replay of the transfer's settlement | Pool | 67,240 | rejected, NullifierAlreadyConsumed | [`JjAbeF…LqWzv`](https://explorer.solana.com/tx/JjAbeFtzfWJ5JH6AyS6Gmz4Rh9dYyHjVtpyXfPzyCuDBwLSQ7Jb7ioPe9HC3AytHY8fgNTSwHyN3G2uVFJLqWzv?cluster=devnet) |
| Transfer with a mutated stage-1 proof | Verifier | 21,453 | rejected, InvalidInstructionData | [`61R9No…UzZL8`](https://explorer.solana.com/tx/61R9NogGVvsjnjwwfiZUwwZ5wvYpLNBrEcrtXierLpiDDyzcji8kjydUQbU9NFYvUaHsdUA7fG3sMVQmSWCUzZL8?cluster=devnet) |
| Withdrawal, stage 1 | Verifier | 1,211,252 | ok, slot 520607963 | [`2QS4o2…gjPpo`](https://explorer.solana.com/tx/2QS4o2i1TpocPc4xeDh9KFBLuKaqBAbSTkiwiNbqecrNoTZvq1rjP8tVyu6BfBGuYFqJnpe4ueG3Ev5q7HvgjPpo?cluster=devnet) |
| Withdrawal, stage 2 and settlement | Pool | 1,153,431 | ok, slot 520608000; vault 2,000 to 1,750, destination 0 to 250 | [`54t54t…jW8EM`](https://explorer.solana.com/tx/54t54tQ14sNpUxU6cQJoi4e1Vpbb8bZhwMrDxmnrUk9fgEPBCmcZi3Qzwmc4F9SjmgoeTXfLDDZ7TfA8QBUjW8EM?cluster=devnet) |
| Replay of the withdrawal's settlement | Pool | 68,841 | rejected, NullifierAlreadyConsumed | [`5LMwbE…H64xW`](https://explorer.solana.com/tx/5LMwbEXuJXPkRphdcoDqRLEEVHFrZ23iobGiTm3Wxy1PXrammxR5EGci5gN9923UXh75kS4CZYQ2NYJLVahH64xW?cluster=devnet) |
| Withdrawal with a mutated stage-1 proof | Verifier | 21,395 | rejected, InvalidInstructionData | [`4T6bRQ…97r4e`](https://explorer.solana.com/tx/4T6bRQT81VHiN573eeNmrUZxVPzPFoQSJ6d3B97AZpB2Xrza7pF5qniqVfBBUXKGoEu7TVTLiwpWhz1PGbC97r4e?cluster=devnet) |

Both spends settled, and the withdrawal moved 250 test tokens from the vault
to the destination. Each replay was rejected because its nullifier had already
been consumed, leaving the protected accounts unchanged, and each altered proof
was rejected by the first stage, leaving the fresh checkpoint unchanged.

The same sequence was also run on a local validator (Agave 4.2.0 with devnet's
feature set), pairing the release verifier at its original pool address with
the frozen pool, and there too both spends settled and every rejection held.

## The October run

On 29 October 2026 the release verifier was deployed to devnet as a new
immutable program, [`CSnhzGdH…zKorQ`](https://explorer.solana.com/address/CSnhzGdHQuzMW512CSunJzHrutcmh8ZAFzqx2z1zKorQ?cluster=devnet), byte for byte the release ELF built from the
frozen source (SHA-256 `63ad3e9c…4299`), and a read-only check afterwards tied
the live program to that ELF. It ran against the existing pool program
[`BmsNikL9…W34Qs`](https://explorer.solana.com/address/BmsNikL97uF7bb1hMnJxsas7a9LjjK8vvT5Q1b7W34Qs?cluster=devnet) and the existing immutable registry program [`9pWwAcBg…6EC9Q`](https://explorer.solana.com/address/9pWwAcBgwhnkA8JWSA6GvjpYqGzSibLF6GqGH8v6EC9Q?cluster=devnet), with fresh
pool state and a fresh registry. The pool build that ran there (ELF
`121f3e29…1548`) predates the removal of the legacy pool instructions on
9 November 2026 and is therefore not the frozen pool. The older pool state on
devnet, which still points at a historical verifier, was left untouched, so no
continuity of its notes or custody is claimed. A transfer and a withdrawal
settled within the compute limit, and replays and altered proofs were
rejected exactly as in the November runs.

| Step | Compute units | Result | Transaction |
| --- | ---: | --- | --- |
| Transfer, stage 1 | 1,214,746 | ok | [`53pTHD…2hhvR`](https://explorer.solana.com/tx/53pTHDfJBmqX7hdxPofSfajURpMhCiB6ceAdMw9ftf3RAXZ6k8D26WaW4MGito2Ty3kRQrAXQSDJ5QBNFsm2hhvR?cluster=devnet) |
| Transfer, stage 2 and settlement | 1,145,305 | ok | [`FNLSBx…RFCxF`](https://explorer.solana.com/tx/FNLSBxjiJ8jPYzE2E25BCgzJ6rm9yrSXnRMgwhj3E5yxwU4wYPfs9vugucr6cVrgnhem2b6TbqPCe3PKjPRFCxF?cluster=devnet) |
| Withdrawal, stage 1 | 1,206,747 | ok | [`3C6fKw…t4F7L`](https://explorer.solana.com/tx/3C6fKwts7pAaTko8kJvBJk4weuUc9y7dfbLTGjRiKuqXo6fWr7xvNoG7w19Nb8V9yY6erAda5jt65khHY5ut4F7L?cluster=devnet) |
| Withdrawal, stage 2 and settlement | 1,154,975 | ok | [`46bYP2…S3wn2`](https://explorer.solana.com/tx/46bYP2Bz1sTiwNDSFxYVumN1kPYa4TARupv8ptAMMx7ixwSNCZwU59WLNDz1zv5V97qgKFp6NtY4njs9rcES3wn2?cluster=devnet) |
| Replay of the transfer's settlement | 67,251 | rejected, NullifierAlreadyConsumed | [`dcqp7k…2Y3zN`](https://explorer.solana.com/tx/dcqp7kp8sq4eeUejKRTPd71TMKkUEhhe8EkkAC29NtJ9PUvPcb3roJfwrs8n65VAPM7CvzwcSVYXs2Jn4S2Y3zN?cluster=devnet) |
| Replay of the withdrawal's settlement | 68,852 | rejected, NullifierAlreadyConsumed | [`La57of…SzAPk`](https://explorer.solana.com/tx/La57ofw95VmBuBuFXx6iziBMdsMRnvMNtCX2ojg1mbhB7iuLmoQVrkucPNxBBpnqWqW4rNJHTWNbWTDXPzSzAPk?cluster=devnet) |
| Transfer with a mutated stage-1 proof | 21,453 | rejected, InvalidInstructionData | [`2N1Eit…gUSX9`](https://explorer.solana.com/tx/2N1EitRqZWRrDFWgSSUsKocjDDQQHaT2u4fgy3aobbE7cKgP9DKbRF7RCW2voJ1SQioa9F2eD7xmaR9ZpesgUSX9?cluster=devnet) |
| Withdrawal with a mutated stage-1 proof | 21,395 | rejected, InvalidInstructionData | [`3Dweqs…v1czb`](https://explorer.solana.com/tx/3DweqsyXeAXbQwefFRppjw1VUbXVjvSctz16oxU552GL5Q87A7G8co4JwwRptgK9EUFEt9cYo9ZbBtSsSkDv1czb?cluster=devnet) |

## What the runs show

The runs show that the verifier runs on a public Solana cluster within the
compute limit, settles a transfer and a withdrawal through its two
transactions with the frozen pool, and rejects a replayed nullifier and an
altered proof. The run of 11 November shows in addition that a payment's rent
comes back when its accounts are closed. That is evidence that the deployed
programs work, and the soundness argument stands on the Lean proofs and does
not depend on it. The function-level proofs were completed for the verifier
of 10 November and are being recompiled against the build of 11 November,
with the theorem statements unchanged. The proofs submitted in all three runs
were made from public test fixtures,
so the runs demonstrate verification and settlement and are not a test of
privacy. The current version has not been deployed to mainnet.

## Where this comes from

The records are on the
[`research`](https://github.com/DJBarker87/aspisZK/tree/research) branch. The
source that the programs of 11 November were built from is on `main`, taken
unchanged from the pinned commit `c7593d23fdc`. The run of 10 November is in
`evidence/devnet-frozen-20261109` at commit `af8f9fd2f9d`,
which holds the signatures of all 69 transactions, a recording of every
transaction with full account images, the rent ledger and the local-validator
record. The October run is in `evidence/devnet-rehearse-20261029` at commit
`07123926e88`.
