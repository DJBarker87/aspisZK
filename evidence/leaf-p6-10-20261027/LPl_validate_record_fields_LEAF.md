# LPl validate_record_fields native P6 bridge

CLOSED on every payload of length0..3712 and every row byte, including malformed
limbs, nonzero high halves, empty payloads, tails and rejected prefixes. No
headline premise removed. Every actual parse_record caller establishes this
length bound through row_shape and record-length checks; K011 checks all row
shapes. No canonicality, previously accepted record or row>=14 premise is added.

For the SAME input bytes/row, the complete native Result, including the SAME
first failing usize index, agrees with
`LPl_Kit_Release.r1_wire.validate_record_fields row bs`. Native Ok becomes outer
`ok (.Ok ())`; native NonCanonical{row,value:i} becomes outer
`ok (.Err (.NonCanonical row (UScalar.ofNat i ...)))`.
`LPl.Validate.native_success/native_error/native_result` export these statements;
`error_bound` proves every returned index<116 and preserves its scalar value,
so the model's out-of-range panic branch is unreachable on the complete domain.

The explicit source-order Scan.Trace has only local done/reject/next cases;
universal native gates construct it. No whole-function equality, independent
accepted run, second input, canonicality or final-result assumption is supplied.
As in LPk, this is a hybrid P6 argument, not Lean elaboration of Rust.

## Pins and complete association

Frozen revision4bb3b3f51e16b4525f1d10336e2b0bcbbd775387,
r1_wire.rs:51–59. The source enumerates chunks_exact32, returns the current
row/index on WideExact decoder failure or nonzero c1, otherwise advances and
returns Ok at exhaustion. parse_record checks row_shape/exact length first and
invokes this leaf only on the field rows. row25's116 words is the maximum.

Model: exact name-only XRk opaque-leaf kit copy, with enum-qualified generated
instance names. No body/tag/type-field edit. LPl_transform.py --check now covers
24 exact copies (the three additional files are unchanged LPc fold simulation,
LPg first-error rule and LPg validator theorem). Co-import L028 fixes the prior
collision context without editing any candidate or old proved module.

| Stage | Accepted evidence | Exact scope |
|---|---|---|
| Canonical/high-zero decoder | Reused LPl K001 and L023 chunk_eq | Every32-byte chunk; the predicate at k=true is precisely the validator's8 canonical words/high-half zero. No stub. |
| Native row/index/error step | Reused LPh K022 `LPh_validate_index` | Every local32 bytes, every row, everyi<116, any prior Ok or original NonCanonical error with earlier<=i. Verbatim source callback agrees with local validator, retaining original errors and the exact current index. |
| Native enumeration/full backing | K010 | Every n<=3712,i<=n/32: actual Enumerate reached via raw iterator nth (no field loop), actual next indexi, SAME32-byte pointer/window, remaining count, successori+1/front and terminal. |
| Natural byte/window join | L039 `bad_eq/window` | Source-selected window equals SAME model drop/take; native base256 decoder equals model validChunk8/highZero. |
| Ordered first error/model | L031 Scan induction; L039 first_error/native_result | All116 stages, immediate error stop, full Option index and full native/model Result. No accepted-only restriction. |
| First-error retention | L036/L037 inherited sticky/error laws; L039 earlier_error | The exact earlier first error is never overwritten; model row/index error is retained. |
| Scalar/error carrier | L039 error_bound; L040 native_success/native_error | Every reached index<116, below cohort usize bound; SAME row and exact index, no model panic on native domain. |
| Uniqueness/non-vacuity | L039 unique/total; K011; inherited L027 zero/rejected chunk | Every byte input has a trace, two traces on SAME bytes have SAME Result; actual native empty/zero success and canonical-high/P-word rejection with arbitrary row, plus all row_shape bounds. |

Native nth is used only to set up an arbitrary iterator pre-state. The function
under proof still uses its original for/enumerate next loop. Advancing raw
chunks without decoding supplies a superset of the actual reachable pre-states;
it adds no assumption that earlier chunks were canonical. Native K010 proves
the current native enumeration counter as well as pointer and count. LPh K022
then consumes that SAME index. Error exits have no digest/oracle operation,
output allocation, mutable callback or visible state to restore.

## Validation, stubs and retained boundary

Stub table: none. No multiplication gate or new trust item. Compiler/platform/
library/P6 association retained. Accepted printed axes are standard only:
propext/Classical.choice/Quot.sound or a subset. L038's dependent-match rewrite
error is retained; L039 is its corrected passing source. Failed sorryAx outputs
are excluded. L040 is the final joined12-name audit with explicit success and
error Results. Each attempt records target,argv,source revision/hash,dependency/
tool pins,exit,wall,RSS,swap and complete axioms/N/A lines.

Every scope is serial/admitted6Ghigh/8Gmax/swap0/tasks64; Lean-M7000;
optimized/offline Kani with fresh frozen graph and unchanged lock each run.
No whole3712-byte decode, increased timeout/cap or unchanged failed shape was
run. Earlier LPh K012 timeout is replaced by separate pure iterator metadata
and the already passing local step/byte-law association, not replayed.

Headline AspisR1.RPx_Deployed.deployed, L154 parameter, frozen3,
RuntimePersistence, narrowed D188, game/failure event/metric unchanged. S2 and
100-bit target not established. No root installation or source-to-ELF proof.
Research crates/programs/lock unchanged; scratch cfg harnesses retained only as
patches/receipts. ELF defaultf8c0ec72…,devnet63ad3e9c…,Pool121f3e29… inherited,
not freshly rebuilt. No release-manifest replay or rebuild trigger.
No session A edits, wallet key cleanup, push or merge.
