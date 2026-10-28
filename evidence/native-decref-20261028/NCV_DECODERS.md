# NCV decoder bodies

Status: budget exhausted; all three complete native bridges OPEN. Concrete model bodies are delivered; no security closure claimed.
Frozen Rust: 4bb3b3f51e16b4525f1d10336e2b0bcbbd775387.
Headline: AspisR1.RPx_Deployed.deployed. No source adoption or trust change.

| Slot | Reference | Extraction | Native equality/control | Installation | Fixture |
|---|---|---|---|---|---|
|48 master|decode_master_ref|E008; L002/L003 PASS|Wrong-length pairs; full bridge OPEN|NCV_Install.op48; sdk_master|Sequence/counter fields proved; full observation OPEN|
|49 checkpoint|decode_checkpoint_ref|E008; L002/L003 PASS|Wrong-length pairs; full bridge OPEN|NCV_Install.op49; sdk_checkpoint|Root/sequence/counter fields proved; full observation OPEN|
|50 lane|decode_lane_ref|E008; L002/L003 PASS|Wrong-length pairs; full bridge OPEN|NCV_Install.op50; sdk_lane|Root/20 digest fields/index proved; full observation OPEN|

Budget: 60 Lean / 60 Kani under the job-specific final allocation. One scope at a time.
Only NCV modules and this evidence directory may change. Scratch source is outside
this repository; all harness changes will be retained as patches. Existing proved
modules, session A worktrees, shipped files and frozen lock are read-only.

## Stage 1: complete reference extraction

NCV_reference.rs contains safe reference bodies for all three wrappers. Helper
errors collapse to Unit because every wrapper maps them to InvalidAccountData;
the Aeneas Result layer remains distinct. The reference uses explicit byte reads,
checked canonical limbs, full master policy/state validation and all twenty lane
frontier conditions. EMPTY is copied from the frozen verifier table (168 limbs).

NCV_E008 extracts all three bodies using the NCO pinned Charon/Aeneas hashes and
nightly-2026-09-17; exact commands, source hash and output hashes are in
NCV_EXTRACTION_PINS.json. No FunsExternal template was emitted. NCV_L002 and
NCV_L003 compile Types/Funs in Lean 4.32.0 against the pinned SInt2 library.
There are no added top theorems in these generated files; axiom audit is pending
for the installation/proof modules. This is reference extraction, not native
refinement or a cohort installation.

Failed experiments are retained: E001/E003/E006/E007 hit the pinned Aeneas
loop-context Not_found exception. E004 identified the separate missing Option
language-item requirement; E005 passes after making that language item reachable.
E008 moves sequence/frontier loops into separate reference helpers, avoiding the
loop-context exception without modifying tools. L001 typechecked but could not
write its output because this job omitted the nested output directory; L002
corrects the own-runner input directory. No timeout or memory kill was rerun.

## Stage 2: typed model installation

L004 proves both directions of the three carrier conversions (and identity/
policy round trips). L005 supplies `NCV_Install.install : AdapterRw.Ops →
AdapterRw.Ops`, assigning exactly op48/op49/op50 to extracted references with
nominal output conversion. It preserves the outer Aeneas failures/divergence
and maps inner Unit rejection to the actual ProgramError.InvalidAccountData.
PDA op38 remains the original slot. JHr can use
`{missing with adapter := NCV_Install.install missing.adapter}`; this installs
bodies, not their still-open native P6 proofs.

L007 proves all-length reference wrong-length rejection, with no finite-buffer
bound. Its preceding L006 draft failed rewriting the Bool guard and is excluded
(including Lean's error-placeholder `sorryAx` audit output). All accepted top
statements print only propext/Classical.choice/Quot.sound.

Native status: K002 KMX positive PASS, K003 matched wrong-copy control FAIL.
K001 was an own wrapper error (empty RUSTFLAGS passed an empty rustc argument),
corrected in K002. K004 direct master/ref comparison on a <=385-byte rejection
union TIMEOUT94.870s/RSS6452428KiB; K005 isolated native Err postcondition also
TIMEOUT94.150s/RSS6460752KiB. No credit, unchanged rerun or cap increase.
K006 splits to EXACTLY383 bytes, arbitrary complete payload: native master
equals reference PASS19.695s/RSS3564688KiB; K007 inverse postcondition FAIL
49.129s/RSS3573092KiB, only its intended contract assertion failed. These
receipts use deployed program features and exact KMX configuration. This is a
wrong-length subdomain only, not a decoder bridge for TX2's accepted384 bytes.
No `stub_verified` Box substitution is used or admitted. Narrow preconditions
cannot be installed as a complete caller law.

Own-runner repairs are limited to input/output paths, the empty RUSTFLAGS bug,
and explicit negative-property source generation to avoid rebuilding unchanged
dependencies when toggling a control flag. From L007 onward direct imported
object hashes accompany the frozen cache manifest and all resolved Aeneas pins.
Lead launchers/admission tooling and shared objects remain unchanged.

## Stage 3: native disposition and symbolic loop laws

Native budget is exhausted:60/60 configured Kani invocations, including failures.
No Box call-site substitution or new function-pointer/Option<fn> credit exists.
K027–K044 selected no harness due an own validator variable collision; all18
are excluded and charged (NCV_RUNNER_FINDING.md). The stricter corrected wrapper
asserts requested/actual target equality. No infrastructure repair was made.

K045/K046 prove/control the ACTUAL frozen `decode_pool_identity_v1` against
reference identity on every144-byte input, collapsing error variants to Unit
as required by the enclosing wrapper. K047/K048 prove/control the ACTUAL
`validate_verifier_policy_v1` success/rejection predicate on every full typed
policy. These are ordinary body comparisons, not verified function contracts
or actual enclosing-call associations. No ghost-pointer precondition exists.

K049–K060 are six paired one-window/fragment checks: four-byte word,
eight-byte word, one sequence write/frame on arbitrary typed pre-state,
checkpoint sequence write/capacity, one lane frontier guard, final empty-root
guard. Every inverse fails exactly its intended assertion. These are fragment
results, not proofs of the original iterators' arbitrary pre-state association.
All used deployed features, frozen graph/lock checks, exact KMX patch and the
K002/K003 copy fidelity pair. LPh-style arithmetic-stub table is empty: no field
multiplication or syscall stub is used.

Both references are retained separately. E010's NCV_CastRef uses safe checked
field casts; its dead cast-error fallback is explicit and the symbolic valid-
window lemmas prove that branch unreachable. E009's unwrap_failed template is
excluded; E010 emits no external template. L023/L024 compile this variant.
The original E008 NCV_Reference remains the primary NCV_Install body selection;
no native equality result is silently reassigned to E010.

Accepted symbolic laws include zero/equality scans, array write/frame induction,
field casts/word reads, full reference sequence assembly, canonical digest
assembly, and sequence-capacity/zero scans. Exact successful target receipts
and audits are in the journal. L045 evaluates all eight master and checkpoint
sequence rows on the actual fixture bytes by row laws, not buffer reduction.
The three complete decoder observations remain OPEN.

## Final disposition

NCV_L060 is the final focused audit:exit0,wall2.203949165996164s,
peakRSS5607200KiB,swap0. It audits all accepted top statements and all six
reference decoder definitions; only standard axioms occur. Budgets60/60 each.
NCV_InstallationSupport proves the selected bodies survive the actual SDK
configuration projection and reuses NCC_/NCF_/NBX_ representability support.
NCV_CopyFrame supplies the KMX value-law window/disjointness composition.

The complete frontier-run draft failed elaboration and is excluded. No complete
JHj decoder observation, full native wrapper equality or new P6 instance is
claimed. The exact member-by-member remaining native AND Lean obligations,
variant/extraction pins, resource evidence and retained host cache are in
NCV_HANDOFF.md. NCV_VALIDATION.json passes source, feature, lock, receipt, axiom
and delivery-hash checks. No release ELF or headline/security-target closure
is claimed.
