# Current Terminal V4 arithmetic soundness packet

This packet freezes the checked focused modules for the current generated terminal arithmetic path. `manifest.json` hashes the copied source files and records the successful receipt data plus direct object pins. The copied receipts preserve their ordered compiler import paths, Lean version/argv, source revision, exit status, wall time, peak RSS, process swap count, and printed axiom reports. Existing evidence subtrees referenced by those receipts retain the selected generated source/model owners.

The proof chain is: exact equality-value loop V9 result; symbolic expected-equality result refinement; current arithmetic source bridge; inversion from actual parts success to the current composition caller; and actual public terminal success to canonical output plus its exact arithmetic value.

This is a component packet, not a complete verifier proof. The V6 endpoint still requires canonical input cells and canonical composition output operands. In particular, the actual composition caller's `composition`, `h1Z`, `copyActive`, and public `mu` canonicality remain explicit in `hoperands`. The packet now includes checked current-source prepared-multiplier construction, component multiplication, `mul_by_r`, and prepared multiplication canonicality. The remaining work is to compose those lemmas through the two actual composition folds and establish canonical semantic/Poseidon callback arrays, selected `h1Z`, `copyActive`, and public `mu`. The precise remaining contract is listed in the manifest.

Superseded diagnostics are separated in `manifest.json`; V4/V5 expanded-product attempts and older projection/caller variants are not dependencies of the green V6 theorem.

The `supporting/` directory now freezes the generated current source cuts and external-template interfaces, the complete focused current-model evidence tree (including superseded failures), and the accepted current object overlay. `manifest.json` hashes every supporting file and preserves the successful module receipts. Historical attempts are intentionally retained as diagnostics; they are not all green dependencies.

The earlier incorrect outer-result projection (`tuple.1` versus a mistaken fourth-field projection) is excluded from V6. V6 derives the tuple equality from `Result.Ok` injection and then uses `Prod.fst`, with the exact first-field equality from `terminal_success_reaches_parts`.
