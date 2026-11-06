# NKV explicit-Result reference

ReviewedTranscription item NKL-RT-batch_tree, under (bc)(4)/(ah), option-A reclassification; not a new runtime or cryptographic trust row. NKV_FRef.lean copies reviewed NKL_ExplicitBody (input hash in NKV_INPUTS.json), adds its complete loop and enclosing functions from the unchanged Port3 body, and replaces the pending-none wrapper with the explicit returned Result. The Boolean carried beside the Result records which three post-loop exits the extractor lost; it is ghost classification only, ignored by f_ref's returned value. No extraction ran.

Frozen source revision 4bb3b3f51e16b4525f1d10336e2b0bcbbd775387; exact numbered body NKV_FROZEN_BODY.txt.

| Frozen source lines | Direct reference correspondence |
|---|---|
| 173 | batch_tree arguments, same proof/queries/root/batch/tree/scratch/hash |
| 174-178 | same lo/hi/n/slot, op4 keys then op5 sort, zero counters |
| 179-184 | loop guard, op9 key, position increment, unpack index and ordinal, op2 opening |
| 185 | op6 leaf before dedup, same hash/tree/opening |
| 186-190 | op8 index comparison then op7 digest comparison; inconsistent duplicate returns explicit Err(Merkle), ghost false; matching duplicate continues |
| 192-194 | exact idx/val update at d then count increment |
| 196 | op11 count then op1 ok_or and Try.branch; residual returns explicit Err(Merkle), ghost true |
| 197 | op3 slot with SAME proof and slot |
| 199-201 | capacity then short-circuit chunks_exact(8).any; explicit Err(Parse), ghost true |
| 202-204 | op10 full verify call and post-arrays; false returns explicit Err(Merkle), ghost true |
| 205 | explicit Ok(()) and complete post-arrays, ghost false |
| 162-170 | batch_merkle_values initializes arrays once, reads three roots, threads arrays through SAME three calls, preserves each Try residual |
| 156-159 | batch_merkle projects roots/queries from SAME Prepared and passes folded_root unchanged |

NKV_L001: complete reference compile exit0, 4.448678738903254s, peak4412596KiB, swap0. NKV_L002: step erasure source theorem compile exit0, 5.252112498972565s, peak4423640KiB, swap0; printed standard axioms. Exact source revision/hash/dependencies/caps/command in receipts. These are support facts; native cut installation, concrete child domains and full ordered-effect transport remain OPEN.
