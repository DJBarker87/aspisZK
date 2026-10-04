# R575 native claim hash-call bridge

R575 proves that, for the actual selected prefix function and the claim bytes it writes, the packed transcript absorb sends a hash input whose flattened address is the defined native claim address. It also connects the actual begin function to that absorb call followed by the actual nonzero sampler. It does not prove the sampler trace, randomness law, shared-oracle transcript, freshness, or privacy/security.

The canonical target is [R575NativeClaimHashCall.lean](lean/AspisV8R19/R575NativeClaimHashCall.lean), SHA-256 `848cc257012b4deb2f70ccd57809b924f3dbbeba40265c95b31c8c907c89717c`. It compiled against the pinned Lean 4.32.0 cache with `-j1 -M4500`, under a systemd scope capped at MemoryHigh 5 GiB, MemoryMax 7 GiB, MemorySwapMax 0, TasksMax 128. The exact successful run was exit 0, wall 1.62 s, peak Lean-child RSS 3,764,692 KiB, swap 0. The output olean SHA-256 is `ecdde43059c2cfe9a60f0aa4cc12e688d9fa902cd85ff865662cac4d76064f16`; it is present in the pinned cache and saved with the evidence.

The proof bridges R569's generated transcript and R156's older representation by preserving the same state array and hash callback. It handles R569's checked Usize subtraction and addition explicitly: `checked_limit` proves `192 - 34 = 158`, and `absorb_map_short` relates checked `34 + data.len` to the wrapping operation under the bound. For the claim, the actual generated QM31 writer contributes 16 bytes and the generated header contributes 2, so `claim_length` gives 18 bytes and establishes the packed branch. The proof then reuses the R167/R206/R205 arbitrary-hash absorb bridge and its packed-address lemma.

`claim_hash_address` proves the flattening equality:

`flatten(actual packed hash argument) = (nativeAddress t q).map decodeByte`

under `data.val = claimBytes q`. `begin_hash_execution` composes that address result with the already proved R573 actual writer and begin-function execution, and leaves the actual `challenge_nonzero_qm31` call in the resulting expression. The arbitrary transcript hash callback remains in the expression, so the proof does not assume a successful hash result.

The six audited declarations report foundational axioms only for five declarations. `begin_hash_execution` additionally inherits `core.fmt.Formatter`, the opaque Aeneas standard-library formatter type already identified in R569. Full `#print axioms` output, exact receipts, and three preserved source/log/receipt attempts are in [r575-native-claim-hash-call](evidence/r575-native-claim-hash-call/RESULT.md). The next proof is the R577 actual inner sampler correspondence, followed by the outer loop and shared-oracle trace law; the sampler and privacy argument remain open.
