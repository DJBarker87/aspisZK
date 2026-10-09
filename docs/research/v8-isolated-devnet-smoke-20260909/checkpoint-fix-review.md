# Eight-lane checkpoint setup repair

Status: live eight-lane checkpoint finalized at **225,796 CU**. The genuine
atomic COMPLETE transfer finalized at **1,083,081 CU**. Both declared 1.2M.
See [live-demo-report.md](live-demo-report.md) for exact signatures and assertions.

## Cause and scope

The frozen sub-1.1M measurement was atomic transfer execution with an injected
checkpoint. The failing devnet instruction was legitimate checkpoint creation
(`AS8C`) over thirteen actual deposits populating all eight lanes. Its strict
decoder reconstructs twenty Merkle parents per populated lane, then seven
super-tree parents. Its simulations exhausted both 1,200,000 and 1,400,000 CU.
These are different instructions, not evidence of runtime inflation in the
same transfer. Failure receipts remain under `evidence/live/`.

The two-note experiment separately confirmed its checkpoint at 1,012,799 CU
(`evidence/live-minimal/pool-checkpoint/`). It does not fix eight-lane setup.

A scalar Poseidon2 experiment passed 10,004 canonical-permutation comparisons,
but also exceeded 1.2M in the eight-lane checkpoint diagnostic. Its code and
failure remain recorded. It is **not selected**. The original Poseidon2 source
was restored by exact SHA256 comparison before the selected receipt build.

## Explicit setup extension

The experimental, default-off `v8_checkpoint_receipts` configuration adds two
instructions. The original AS8C, account formats, hash domains, proof grammar,
verifier checks and atomic terminal instruction are unchanged.

* `AS8V || [1,lane_id,0,0]`: accounts `[master, lane, receipt, payer, system]`.
  Authenticate the master and lane PDAs, ownership, full canonical encoding,
  frontier and root using the original strict decoder. Only after success,
  create or refresh a receipt through supported System Program instructions.
* `AS8K || [1,8,1,0]`: original twelve AS8C accounts followed by receipts 0–7.
  Authenticate every receipt owner and PDA, its fixed format and lane binding,
  and require **all 768 lane bytes** to equal the recorded validated image.
  Recheck canonical structure and bindings, compute the original seven
  super-tree hashes, call the original pure checkpoint planner, and create
  the same immutable checkpoint and master update.

Receipt PDA seeds are `[b"aspis-v8-lane-validation", lane_pubkey]`. Its 808
bytes contain magic/version `AS8V\x01\x08\x00\x00`, lane pubkey and the complete
lane image. Only the strict-validation instruction writes this PDA family.
Receipts are reusable and permissionlessly refreshable after a new strict
validation; there is no receipt close path. Rent remains in the isolated PDA.

Preparation can happen at different times, but finalization reads every live
lane in one transaction and requires exact equality with all validated images.
Any intervening lane-byte change rejects. There is no hash-only cache and no
new assumption that a Pool-owned lane is intrinsically valid. The internal
fast parser is used only **after** receipt authentication and full equality.
The original decoder's full-capacity semantics are retained, not strengthened
or advertised as new formal closure.

This explicitly changes checkpoint **setup**, adding eight preparation
transactions. It does not split COMPLETE verification or atomic settlement.
No root check is removed; its evaluation is bound to the exact bytes consumed.

## Executed regression

The diagnostic injects the preserved finalized eight-lane snapshot locally;
that injection is **not live evidence**. Receipt creation and checkpoint
persistence execute the actual rebuilt SBF using TxV1 and a declared 1.2M CU.

| Operation | Measured local CU |
| --- | ---: |
| Lane 0 validation | 423,587 |
| Lane 1 validation | 420,591 |
| Lane 2 validation | 423,589 |
| Lane 3 validation | 419,050 |
| Lane 4 validation | 419,077 |
| Lane 5 validation | 419,110 |
| Lane 6 validation | 419,070 |
| Lane 7 validation | 435,580 |
| Atomic checkpoint finalization | 237,796 |

Simulation and execution CU agree. The checkpoint and master byte images
match the canonical host planner exactly, and all lanes remain unchanged.
Bad root, bad frontier, stale lane, wrong receipt owner, corrupted receipt and
swapped receipts all reject. Preparation failures create no receipt; final
rejections leave master/checkpoint unchanged. Detailed controls and build
resource metrics are in `evidence/checkpoint-receipt-*.log`.

Selected Pool: 537,728 bytes, SHA256
`e07dc1e7445a0256c6da7a9833e7946cc0225e9076db1dd350f914dac500d108`.
Fresh Pool identity: `CWc8x6vhwX5UUUwNE6ys5vjT5vPUYahHu1JmEG8DtJMr`.

Rebound COMPLETE verifier: 941,672 bytes, SHA256
`a4dd7d5ab699cd32fececb5f8a382df8e2f2f9bf6f6810b865d5a9084606eaab`.
Fresh verifier identity: `9Q2m6188rFLiWdYnttKYhMjbfarQXdq9D4HzS23eTkqc`.
The changed verifier input is the Pool capability identity; lifecycle and
selected COMPLETE kernel remain unchanged. Neither image is claimed identical
to the original selected verifier ELF.

## Remaining live gate

The immutable first-run programs remain retained. No upgrade is attempted.
Funding is restored by an authorized 8-SOL transfer from dedicated Colosseum
devnet test wallets, within the original 25-SOL budget. All keys are retained.
The new Pool retains its upgrade/close authority. The verifier is deployed
with authority retained until successful live setup and lifecycle checks;
Registry V2 certification then requires making only the verifier immutable.

The new setup and genuine transfer are now measured live, with exact settlement
assertions and malformed/replay controls passing. Formalisation and
production-activation claims are unchanged. Public funding and deployment receipts are under
`evidence/live-checkpoint-fix/`.
