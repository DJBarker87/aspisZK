# Shape / scan: concrete source binding remains open

Branch codex/cx-row-shape-20261025. Requested shape/op3 and scan/op4 rows are
NOT CLOSED. S2 and the 100-bit target remain not established.

## Checked findings

1. `RowShape_InstalledSlots.shape_slot` and `scan_slot`: the EXACT verifier
   dictionary passed into sdkOps in accepted_pair_claims preserves supplied
   CurrentCaller Ops.op3 / Ops.op4. `sdk_dictionary` identifies the installation.
2. `RowShape_SlotObstruction.shape_success_not_parser`: a permitted supplied
   dictionary accepts empty bytes with S1 while frozen parseReached rejects
   those same bytes for every transcript.
   `scan_success_not_canonical`: a permitted dictionary's scan succeeds on
   symbolic zero padding followed by ff ff ff ff at offset7031, while the
   frozen complete scan fails. These are LOCAL CALL witnesses, NOT accepted
   native transaction witnesses. They do not refute a future contextual theorem
   with concrete native body instances, or invalidate the actual Rust parser.
3. `RowShape_Tx2Boundary.authenticated_tx2_slot`: sdkOps retains the ENTIRE
   adapterOps.op11 authenticated-TX2 child, polymorphically over digest state.
   `same_cut_tx2` uses the identical supplied D189 f,s and SourceCuts to export
   that exact dispatch success; it selects no replacement execution. This is
   an INTERNAL cut projection, not a new top-level SourceCuts admission or a
   TX2 parser/scan interpretation.

## Exact obstruction and next deliverable

accepted_pair_claims is parameterized by arbitrary CurrentCaller Ops and
AdapterRw.Ops. Its candidate installation concretizes other slots, but does
not identify these parser/scan slots with source bodies, nor install the TX2
body. A theorem about this entire parameterized family cannot infer a full
parser law from a successful local shape/scan result alone, as the checked
witnesses show. This packet DOES NOT prove that the requested contextual
same-accepted-execution theorem is false. It leaves that item unproved rather
than introducing a whole-parser-success hypothesis or silently changing the
installation. Existing retained entry/scan/child/ROM premises keep their exact
scopes; they are not discharged here.

The actual Rust `parse_shape` (candidate.rs:40) is header-only. Full frozen
`parseReached` includes header, nonsemantic scan, semanticRows and transcript
alignment; the latter come from later source calls. Thus a successful header
body is not by itself the frozen combined parse stage. The full Rust scan at
:54 covers y1, inactive, round0, round1 and all22 openings; a y1-only certificate
cannot instantiate it. Existing stage2 extracted parser successful_variant
is a separate explicit-ops source certificate, not an installed Claims slot.

Next concrete deliverable: bind source parse_shape and the WHOLE canonical_scan
Result/effect implementations to the retained Ops.op3/op4, bind the enclosing
native authenticated TX2 child to adapterOps.op11, then compose header/scan/
semantic-prefix/transcript laws in source call order on the SAME cuts from
accepted_pair_claims. A newly concretized base dictionary needs an explicit
native extraction association; it cannot silently be identified with every
previous arbitrary base. No new security or crypto assumption is proposed.

## Validation, resources, freeze

Six Lean attempts, three successful final modules; 0 Kani/Rust/SBF runs.
Every attempt ran one module on the approved coherent SInt2 workspace, reusing
its objects, with lake env lean -j1 -M7000 -DElab.async=false, fixed systemd
MemoryHigh=6G / MemoryMax=8G / MemorySwapMax=0 / TasksMax=64. No cap change,
memory kill, wall timeout, unchanged retry, infrastructure edit, package build
or full frozen replay. One namespace error caused a cascading heartbeat timeout
in001; source changed before002.003's broad simp hit recursion depth;004 uses
symbolic padding.005 needed explicit polymorphic field equality;006 fixes it.
Failed receipts and their source snapshots are retained; diagnostic sorryAx is
excluded. No explicit sorry/axiom/admit/native_decide or limit override exists
in the final modules. Only propext, Classical.choice, Quot.sound occur in EVERY
new top theorem's successful #print axioms output.

| Attempt / final target | Exit | Wall seconds | Peak RSS KiB | Swap | Source revision |
|---|---:|---:|---:|---:|---|
|002 / RowShape_InstalledSlots.lean|0|2.0982766329543665|5231688|0|a59efe534c|
|004 / RowShape_SlotObstruction.lean|0|2.375994873989839|5347464|0|42f96602a3|
|006 / RowShape_Tx2Boundary.lean|0|1.8820829570177011|5231508|0|3014ad9aa8|

Exact commands, source SHA256s, dependency object/sidecar fingerprints, dirty
source flags, cgroup checks, complete errors/axioms and time metrics are in
RowShape-001 through006 receipt.json/stdout.log/time.log plus source snapshots.
source-boundaries.json pins source inspections and the inherited closure
manifest. These are focused cached checks, not a coherent new release replay.
Budget consumed 6/100 Lean, 0/60 Kani; stopped at the source-binding frontier,
not budget exhaustion. git diff --check passed.

Discharged assumptions: NONE. Added/changed assumptions: NONE. Retained:
all source-instance, SDK/std/allocator/runtime/extraction/history/oracle/child
premises of accepted_pair_claims and its D189 boundary. Quantifiers, carriers,
failure event, security contract and metric unchanged. No same-cut or caller
output premise was added to accepted_pair_claims.

Only new RowShape_ modules and this evidence directory changed. No session A
live worktree/candidate, existing proved module, shipped file, cfg(kani) source,
key, feature, wire format or parameter changed. No ELF rebuild trigger. Pins
below are inherited, NOT freshly reproduced:

- default f8c0ec72621fd5029a97d796c4a3623d0dc44a8e7074122372f9872915d143d4
- devnet 63ad3e9cc096dcbb55b3ca7ac7c8e89e6a845796ab5e4f5b7d15db96f3784299
- Pool 121f3e29741f510e6dc42d0345fc3c36217600f0be337094855c4a9da2581548

No objects/binaries/tarballs committed, no push. All launched jobs terminal.
