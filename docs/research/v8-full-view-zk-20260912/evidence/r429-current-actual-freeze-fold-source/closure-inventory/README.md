# R156/R160 freeze gamma closure and fold inventory

This is a read-only index over the frozen R156 and R160 LLBC artifacts and the already generated R156 Lean source. The JSON files preserve the complete selected LLBC function/type rows and the entire fold-call statement nodes; they are not normalized or semantically rewritten. `build_inventory.py` regenerates these outputs from the paths and hashes in `input-source-hashes.json`.

R156's freeze root is `fun_decls[0]` (`aspis_v8_performance_host::freeze`, `relation_callback.rs:127:0–145:1`). The outer closure implementation rows are functions 23/24/25 (`call_once`, `call_mut`, `call`); inner closure implementation rows are 282/283 (`call_once`, `call_mut`). Closure type rows 18 and 65 carry the captured fields: type 18 has one `&Free(0) Deduplicated(540)` field; type 65 has `&Free(0) Deduplicated(540)` mutable and `&Free(1) Deduplicated(540)` shared fields. The generated R156 type aliases identify these as `QM31` and `QM31 × QM31` respectively (`Types.lean` lines 140–145).

The outer closure's whole fold call is statement 18 in function 25. In R156 it targets `fun_decls[176]`, the opaque `core::slice::iter` fold declaration. In R160 the same call position targets `fun_decls[177]`; that declaration has a structured body spanning the pinned core source `file_id 38`, lines 259–289. The complete R160 function row is preserved in `r160-slice-fold-implementation.json`. This records declaration/body structure only.

The corresponding generated Lean call is copied verbatim to `r156-generated-fold-call.txt` from `Funs.lean` lines 1612–1626. The source excerpt containing the batch closure and gamma capture is `frozen-rust-gamma-closure.txt`. Input LLBC/source/Lean SHA-256 values and byte sizes are in `input-source-hashes.json`.

These artifacts identify declaration rows, call sites, and serialized type identities. They do not establish Rust-to-Lean execution correspondence or any semantic/security conclusion.
