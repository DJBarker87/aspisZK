# LPb P6 leaves — final handoff

**Both bridges OPEN. Target not yet established. Actual-top premises removed: zero.**
This job uses the final 20-Kani/60-Lean scope, not the superseded L187 replay.

## verifier::prepared_claim — OPEN

Checked supplied-model factorization:
`LPb_PreparedSequence.prepared_model_stages`, consuming
`LPb_ClaimStages.part_model_stages`, gives the exact six-point sequence of
29-step dot folds, seven powers, and the ordered weighted fold. Theorems
preserve the supplied Result/Option/panic/divergence behavior. They do not
assume a native equality or turn a Kani result into a Lean axiom.

Native bridge stages so far:
- `LPb_K003` actual EbyKDot::push return condition on arbitrary canonical E and
  arbitrary raw K: PASS, including both success and rejection covers.
- `LPb_K008`–`011` actual rejection/empty-post-state frame for each independently
  noncanonical scalar limb: PASS.
- `LPb_K002` unrestricted one-push reference/post-state+finish: TIMEOUT.
  Its 29-repeat successor was not launched. `LPb_K012` rejection frame after
  ONE arbitrary valid push also times out. These establish no post-state law.
- `LPb_K006` exact operand-order seven-power comparison: TIMEOUT.
- Whole private prepared_claim binding, semantic scalar selections0–4, general
  reached Dot state/finalization, and seven-part weighted accumulation remain
  OPEN. Public-helper calls are not described as calls to the private function.

First source-order open stage: powers::<7>(kappa), verifier.rs:54. The first
nontrivial split powers::<3> also times out (K018); neither commutation nor a
coefficient restriction was introduced. Later, source canonical::Q::raw / two
private Dot sum updates and finish on arbitrary nonzero canonical operands and
reached history remain OPEN. Model factorization does not discharge them.

## verifier::checkpoint — OPEN

Checked supplied-model factorization:
`LPb_CheckpointSequence.checkpoint_model_stages` and `.erase` identify the exact
supplied checkpoint model with the named stage sequence and its logged version.
`LPb_CheckpointAttempts.successful_stages` records attempted calls in order:
`[proof]`, `[public]`, `[label,payload]`. First/second error attempts are retained.
The native full-call result/order/byte bridge is NOT thereby established.

Native stages:
- `LPb_K004`: actual QM31::write_le_bytes equals the four-word owned reference
  for every raw four-limb u32 value, all16 output positions: PASS.
- `LPb_K005`: actual WideExact::to_le_bytes equals the eight-word reference
  for arbitrary canonical E, all32 output positions: PASS.
- `LPb_K007`: actual public checkpoint versus owned reference, S2/64 weights,
  three/five-byte physical proof/public, repeated arbitrary E/K fields and
  concrete Trace dictionary: TIMEOUT. No serializer stub was installed.
  Even a PASS in that domain would not prove full arbitrary-input P6.

Exact open native stages: enclosing header/proof/public/state/roots/query and
scalar loop correspondence on the SAME full input, complete attempted digest
order, arbitrary digest answers/physical carrier lengths, and returned
payload++checksum/size. Allocator/heap/ownership qualification remains explicit.
A successful supplied-model trace is not evidence of native chronological calls.

## Attribution and completion

No new Lean axiom, sorry, admit, native_decide, heartbeat/depth override, trusted
item, source adoption, shipped cfg(kani) edit, or release artifact is introduced.
No ELF rebuild trigger fires; the three historical ELF hashes are inherited,
not reproduced. The two leaves remain visible P6 obligations for XRn_.

Final validation and per-stage results follow below.

## Final native stage table (20/20 budget used)

| Runs | Result | Exact additional scope |
|---|---|---|
| K001 | CLI error | No verification launched; corrected timeout flag in K002. |
| K002 | TIMEOUT | Arbitrary one-push native Dot vs explicit wrapping reference. |
| K003 | PASS | Arbitrary raw K/canonical E push-return condition, fresh Dot only. |
| K004/K005 | PASS | All16 raw scalar / all32 canonical-wide byte positions. |
| K006/K018 | TIMEOUT | Powers7, then powers3 first nontrivial split; exact operand order. |
| K007 | TIMEOUT | Actual checkpoint/reference, stated restricted carrier/dictionary domain. |
| K008–K011 | PASS | Four separate noncanonical-limb rejection/empty-output frames. |
| K012 | TIMEOUT | Rejection frame after one arbitrary valid push. |
| K013 | PASS | 29 independent canonical scalars, all wide values ZERO; restricted identity only. |
| K014 | TIMEOUT | Actual29 pushes, independent unrestricted reached inputs, return conditions only. |
| K015 | TIMEOUT | 64 independent raw scalar serialization/append steps. |
| K016 | PASS | Six independent canonical-wide serializers, all192 output positions. |
| K017 | TIMEOUT | Full29-cell canonical-y1 construction and selected field read. |
| K019 | PASS | Actual16-byte scalar writer in arbitrary32-byte surrounding buffer; full frame. |
| K020 | PASS | Actual field(y1,l), l<29,928-byte input, arbitrary canonical selected E and arbitrary surrounding bytes; l28 covered. |

K015 splits at its scalar writer (K004/K019); K016's primitive is K005.
K017 splits to ONE selected field with arbitrary surrounding bytes (K020).
K014's first push return split is K003; its arbitrary post-state is still OPEN.
The unrun dot_29 harness is retained as an explicitly unused candidate, never
counted as a verification. No failed/timed-out shape was rerun unchanged.

Kani total:11 PASS /8 CBMC90s TIMEOUT /1 CLI error. Wall872.534616910s,
peak process RSS5713764KiB, cgroup memory peak5862879232bytes, swap0.
Every receipt retains the exact argv, revision/source hashes, admission, verified
6G/8G/swap0/tasks64 limits, exit, wall, RSS, cgroup peak, and complete output.
No further Kani invocation is permitted in this scope.

## Active harness lock qualification

Final inspection found cfg-if/libc version drift in the active standalone
harness lock despite exact direct native source/root-lock pins. See
LPb_LOCK-FINDING.md and the retained LPb_Cargo.lock. All native outcomes above
are for that recorded HOST graph; they are NOT frozen-dependency or ELF
certificates. This is another open replay gate, not a trusted item and not
silently repaired after budget exhaustion. Both full P6 leaves stay OPEN.

## Final Lean audit, accounting and stop

L037 imports the current18 proof modules, checks all47 theorem statements and
prints all47 axiom sets. All use only propext/Classical.choice/Quot.sound or a
subset. Source creation is explicit (`autoImplicit false`) throughout. The
same-run model result is `LPb_CheckpointNativeGap.model_trace_bytes`; six-part/
seven-power bounds are `LPb_PreparedWitness.trace`; the actual model payload
width is `LPb_PayloadWidth.payload_width` (1736 at64 weights/six wide bytes).

Lean used37/60:31PASS/6FAIL. Wall66.500490579s, peak RSS2655912KiB,
cgroup peak323878912bytes, swap0. Failed candidates are retained and excluded
from accepted evidence. No cap increase, memory kill, unchanged timeout retry,
parallel own scope, reservation bypass or full release replay occurred.

Kani20/20 is exhausted. The other23 Lean attempts are unused; the remaining
native-stage and active-lock replay gates need native evidence, not more model
wrappers. No further native invocation is made. This is an OPEN handoff, not a
claim that the requested complete per-stage native bridges were delivered.

LPb_recount.json pins identical complete FJv_Top.deployed before/after sources.
Removed/added/changed0/0/0; ledger method atomic quantified families, SAME
witness, shared once, L185=L159 alias; deltaT0/P0/G0/C0. No quantifier, carrier,
failure event, conclusion, game, metric, trust item or security target changed.
Local Kani covers and LPb_Nonvacuity witness nonempty stage domains only;
no joint actual-top inhabitant is asserted. S2/100-bit target not established.

LPb_cleanup.json records322169210 bytes of own build/object/.lake/crate cache
removed after checking the final selected object hashes. No own live compiler
or solver remained. All16 /tmp solver candidates predate this job and were left
untouched; shared coherent/XRn caches and every source/receipt/key are retained.
No shipped/cfg(kani) file changed; no ELF rebuild trigger. Inherited, NOT newly
reproduced: default f8c0ec72621fd5029a97d796c4a3623d0dc44a8e7074122372f9872915d143d4;
devnet63ad3e9cc096dcbb55b3ca7ac7c8e89e6a845796ab5e4f5b7d15db96f3784299;
Pool121f3e29741f510e6dc42d0345fc3c36217600f0be337094855c4a9da2581548.
