Exact withdrawal public validator extraction input

extract.py copies fourteen declarations without changing bodies, signatures,
errors or check order. It records source file/revision hashes and byte/line
spans, then inserts each fragment verbatim into a namespace-only layout.
Run extract.py --check to verify all retained identities. The cut script does not modify production source. The dependency-free Cargo package is tool input, not a claimed
production crate build.

The target is the existing validate_pool_v1_withdrawal_public_v1 in
crates/aspis-statement/src/pool_v1/payment_relation.rs:239. Its explicit
dependencies are withdrawal_common, validate_common, digest_is_canonical,
CommonPublicV1, the exact withdrawal/error types, M31/Digest and constants.
There is no hashing, allocation, Solana account operation or field arithmetic
in this target. Standard array equality, booleans and Result
operations still require inspection of the emitted dependency closure.

The checked Amount431.success_amount_guard theorem starts from the actual
generated function's success and derives 0 < public.amount.val and public.amount.val < 2^30. This differs from
M31 canonicality, which alone allows zero and amounts up to P-1. A successful
helper theorem is not a proof that an arbitrary caller reached this helper.

The admitted stage1 path decodes ASF8, whose withdrawal decoder and validator
call this payment validator. Admitted stage2 decodes ASQ8/ASWP and constructs,
validates and encodes ASF8, again calling it. Exact source call locations and
the remaining metadata/account/checkpoint obligations are documented separately.

run-local.py uses pinned existing local tools, an offline dependency-free
lockfile and one Charon/Aeneas attempt. The 3GiB sampled process-group kill
threshold leaves margin below the authorized 3.5GiB ceiling; each command has
a 180s timeout. This is a sampled guard, not a cgroup. Evidence retains source,
tools, commands, resource receipts, LLBC and generated source. Extraction
identity is not a proof of compiler, model or Rust runtime correspondence.

The associated evidence bundle withdrawal-validation-source-431-20261015 retains
two rejected iterator-based attempts and the clean fixed-eight-check extraction.
It also checks digest_success_iff for every fixed-width digest, records native
differential and existing validator tests, and retains all compiler/axiom receipts.
