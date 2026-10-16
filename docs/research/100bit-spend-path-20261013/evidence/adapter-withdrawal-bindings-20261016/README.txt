Actual reconstruction withdrawal metadata bindings, Lean4.32

This checkpoint adds one proof module above 2405d1deb and C's exact extracted
reconstruction e97ac2bb0. It does not alter Rust, generated definitions, the
existing naming adapter, backend, or any live protocol module.

terminal_metadata_bindings inverts actual terminal-validator success through
the output-lane guard. reconstruct_withdrawal_bindings composes actual
reconstruction success and the request's exact Withdrawal payload. The twelve
consequences pin index-step, asset, nonzero account keys, lane range, pool,
deployment domain, snapshot pool, checkpoint sequence/root and actual output
lane. It imports only ExtractedAdapterReconstructSuccess. The private symbolic
array comparison helpers reuse Aeneas's eq_homo_spec; no nominal Terminal cone
or full late/tree-validator equality is imported.

The one changed target passed its first check in 2.815 seconds, with two
standard-only axiom reports, sampled cgroup peak629637120 bytes and zero swap.
Exact process RSS, runtime/source/import/object hashes and the 6GiB high/8GiB
max/swap0 scope are retained in the receipt. Four predecessor objects were reused
from their checked receipts; their producing checks are in the previous
adapter-public-bridge-20261016 bundle. Other retained successful-target receipts
are provenance records, not new compile claims. A missing metadata directory
caused one pre-Lean staging failure, recorded separately; no proof attempt failed.

The 39-member archive retains the run, source manifests, exact current source,
predecessor receipts, immutable external snapshot, import-link journal, final
object and collection utility. verify.py independently checks these hashes,
the exact two reports and final source/object. No predecessor replay is needed.

The AuthenticatedAsq8Accounts input remains a structural value. These facts do
not prove its owner/PDA/account authenticity, custody, request admission, or
runtime reachability. Actual semantic serializer success hs, supplied-public
hbind and cross-stage same-byte/checkpoint provenance remain explicit and OPEN.
Stage1 [3,10]/[3,11] calls the serializer; ASQ8 stage2 does not. Rust/extraction
tool correctness remains outside this Lean result.
