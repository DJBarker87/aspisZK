# Full current WideExact multiplication source graph

PROVED: the full current generated WideExact::mul graph maps exactly to the checked canonical-total multiplication owner. The imported full-field extraction has no opaque lower-field operations. This new graph theorem reuses the existing CurrentWideBaseBridge/CurrentWideQMBridge conversions and adds exact QM31 subtraction and mul_u graph bridges. It preserves failure/divergence as well as success.

PROVED: on canonical inputs, the complete generated source multiplication is total and its result is canonical. Successful actual source multiplication also preserves canonicality. Neither theorem adds a backend-operation semantics premise; lower-field and QM31 behavior is supplied by the retained checked graph/arithmetic proofs. Input canonicality remains explicit. This is an arithmetic totality/range dependency, not whole-verifier totality or soundness.

The selected CurrentWideMulSourceGraph source is pinned in the manifest, with the exact imported CurrentWideField and CurrentWideMulCanonical objects. Five exported axiom reports contain only standard axioms. Focused NUC Lean4.32 check: exit0, 1.905 seconds, process RSS 3,695,796 KiB, cgroup peak 371,404,800 bytes, zero swap, no cap events; High1GiB/Max2GiB/Swap0 and -M4400. Shared mapped import pages are reported separately from cgroup accounting. No unchanged dependency replay or production source edit.

Current field.rs and wide_exact.rs equal the exact whole-file inputs of the retained no-opaque extraction; their hashes and current revision are recorded in current-source-identity.json. The retained source checker was run once without a Lean replay. The field extraction and compiler/source preservation trust boundary is unchanged by the graph theorem.

OPEN: mathematical degree-eight multiplication decoding, other WideExact operations required by finish/fold, caller canonicality/reachability, the powers array/from_fn borrowing owner, nominal carrier links at parent calls, final freeze/deployed artifact correspondence and the complete 100-bit theorem. This packet does not close S1/S5/R22 as a whole.
