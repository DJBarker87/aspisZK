# S6 current release-source reconciliation — 26 October 2026

This packet closes the historical-to-current **component source identity**
obligation for the statement crate and the four first-stage caller functions.
It does not close S6, S1, S2, or the 100-bit soundness target.

The authoritative release ledger at research `5619adf619c2d384b7969990e70009e524ca8358`
pins compiler source `4bb3b3f51e16b4525f1d10336e2b0bcbbd775387`.
The historical component freeze is `25866ec331cc7ce27dd9956609c11d32fa8fa58a`.
The source-only manifest records both SHA-256 values for every tracked file:
all 84 statement-crate files, including Cargo.toml and all helper modules,
are identical. This extends the historical statement source identity pins to
the release source. It does not extend historical tool/import/runtime scope.

The complete bodies of `observer`, `error`, `first`, and `first_decoded` in
`programs/r1-cost-probe/src/lib.rs` are also identical, as is program Cargo.toml.
The caller passes `statement.semantic_public()` and the original public byte
slice to first_decoded; first_decoded passes observer() to tx1. The release
observer is None with cu-profiling disabled. Whole lib.rs is not identical.

The current owned adapter is explicitly pinned separately. It did not exist
at the historical freeze, so no historical adapter equivalence is inferred.
Its stage1_owned body decodes public_data once and passes that statement's
semantic public and the same public_data to first_decoded. This source
inspection is not a proof of actual SDK/account execution correspondence.

The core inventory includes all 89 tracked files; precisely
`state_only_prefix.rs` changed. The complete change replaces the [7,6] loop
with two assignments. The checker verifies that this is the entire byte
delta and retains its patch; this packet proves no semantic equivalence for
that delta and does not duplicate the other cone owners. All core source
identity and whole dependency-closure claims remain appropriately scoped.

Existing checked evidence reused, without compiler replay:

- S6OuterNativeCodecV1: accepted actual native decoder output re-encodes to
  all original 1,880 bytes, both variants. No codec law input.
- S6CurrentNamedForestPortV1: the named full-forest roundtrip premise is
  discharged in the accepted source consumer. ChildInputRetention and the
  cross-transaction reconstructed-statement identity remain explicit.

The checker revalidates source/receipt/import pins through both maintained
packet checkers, successful status, zero swap and all standard-only axiom
reports. Exact reused proof receipts and their original wall/RSS/axioms are
in manifest.json. They are not new compilations under the current freeze.

Lead SAP_FrozenSource/SAP_FrozenSdk/SAP_PrepareOwner source snapshots were
reviewed at the immutable research revision above. The installed preparation
owner now supplies SessionAPrepare on the same actual source run; the enclosing
SDK theorem still explicitly requires AeneasExtraction, SDK borrow/runtime
admission, allocator/std interpretation, query/geometry primitive instances,
and other cone/trace/checkpoint interfaces. Those proofs were not recompiled
or promoted to native release correspondence by this audit. No overlapping
SAP or primitive proof work was started.

Remaining S6 deployment row L176 is native Box/ownership/initialization/error/
cleanup correspondence for the source getters and public decoder. Actual
stage1 extraction/library binding remains with the S2 owner (L179), and
source-to-ELF lowering with S10 (L186). The updated ledger records L177 Claims
std slots as removed at the selected helper scope; that does not discharge
L176 or the whole library boundary. No source adoption is requested by this
packet. Any future candidate still needs equivalence, adoption and affected
source/tool/import/artifact re-pins.

Validation: `python3 tools/s126-current-freeze-20261026/check.py`.
This is focused-extractor-proof-packet-v1, source-only; no Lean, Kani, extraction,
SBF build, binary, custom axiom or resource override. The initial audit preflight
failed on an incorrectly indented expected core delta before any packet was
written; the expected literal was corrected to match the exact Git patch.

Successful source audit: exit 0, 7.824052s, self RSS 22429696B, maximum child RSS 48693248B, swaps 0. #print axioms: N/A (audit); reused Lean reports are retained verbatim.
