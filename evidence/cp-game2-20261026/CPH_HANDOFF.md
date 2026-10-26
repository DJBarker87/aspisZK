# CPH checkpoint game continuation

**Target not yet established; full completion is not claimed.** The requested
nine targeted antecedents are absent from the actual new top, and the program
pin and both transaction trace instances are derived. The requested **full joint
accepted cryptographic/source/frozen3 fixture remains open**. Lean budget is
exhausted: **100/100 actual invocations**, 88 successful, 12 excluded development
failures; Kani **0/10**. No further prover job is authorized under this budget.

Branch `codex/cx-cp-game2-20261026`. Worktree remains isolated. No push or merge.
Only `lean/CPH_*.lean` and `evidence/cp-game2-20261026/` changed.

## Established root and exact changes

`AspisR1.CPH_Top.deployed` is the adopted frozen3 root. Its source result comes
from **actual `Rc2_Top.deployed`**, through `CPH_Rc2Source.source`, then
`CPH_Pair.accepted` and `CPH_Close.from_rc2`. The extraction tactic in
`CPH_Extract` inlines only the checked Rc2/T2R root proof bodies, projects source
conjuncts and refuses any remaining metavariable for unprovided obsolete headline
arguments. The resulting ordinary proof is kernel checked with standard axioms.
This is proof refactoring of a source branch independent of the old headline,
not an inference from an arbitrary implication with an unproved antecedent.

The SAME original f,s,run,tx2 and NP6 contents remain. Both original history
continuations are applied internally to a constructed version. The result exports
version.key = TX1.slot2 = TX2.slot6 and version.events = physicalEvents. Source
copy/frame, Rc2 events, frozen3 cost/relation/runtime/account-sum bounds remain.
P2Prime, FirstEntry, the frozen3 accepted canonical join and StoredCarrierBinding
remain visible. The account experiment is still the explicit GExq wrapper carrier;
it is not silently identified with an unspecified deployed failure event.

`CPH_Game.DeployedPairExecution` has exactly four fields, quoting amendment
(a)-(d). Its eleven expanded clauses are inventoried in the ledger JSON. Field(d)
contains BOTH state-threaded physical traces: TX1 suffix after the native copy,
and TX2 from its loaded bank. `CPH_Trace.derive` proves their CPP instances;
`CPH_Recorder.physical` proves equality with the existing CPS source recorder under
the retained extraction/P1/syscall items. Both are exported by the top. No fifth
field or separate trace/refinement hypothesis remains.

`RuntimePersistence` is one named explicit hypothesis of exact type
`CPR_DataPersistence.TwoTransactionLaw`, never a Lean axiom. Owner/marker/funding
are derived at the accepted writer's actual bank/key. Pure op36/clone interpretation
and NP6 installation are selected together in `CPH_Install`.

The free program/programNotSystem inputs are removed. The program is the public
address `7Q2nGsPg8rbjdxKHK4jxTgEWLTyd9o1X4KMSjCieRmue` from the retained
successful exact-default-ELF loaded-program receipt. `CPH_Program.not_system`
proves its first byte differs from the system key. `CPH_PROGRAM_PIN.json` links
that receipt to retained L186/lowering2 evidence under existing P7. This fixes the
recorded default deployment, not every future address or mainnet registration.

## Before/after and recount

`CPH_BEFORE/AFTER_Top.lean.txt`, `CPH_BEFORE/AFTER_ELABORATED.txt` and final audit101
retain the exact source/elaborated statements. `CPH_LEDGER_DELTA.json` follows the
atomic quantified-law-family method, preserving shared existential witnesses and
splitting conjunctions rather than counting a structure as one premise.

Targeted history families L094/L095/L096/L180: **4 -> 0** antecedents. Protection
Rc2_P001-P005: **5 -> 0** guards at the actual writer CP. Scoped targeted delta:
**-9**. The authorized game has **11 expanded event-domain conditions**, and
RuntimePersistence adds **one T family**. Counting every game leaf mechanically
as a P condition instead gives **9 -> 11 (+2)**. Neither count is hidden.

Quantifier changes are explicit: independent entries become the owner-approved
correlated experiment; arbitrary-bank protection is specialized to the accepted
writer CP; program identity is fixed to the recorded deployment; the headline
moves to owner-approved frozen3. No theorem asserts that every arbitrary bank/key
is verifier-owned, initialized or funded. No unconditional global release ledger
totals or completed 100-bit security result are certified.

`CPH_Rc2Top.deployed` additionally calls Rc2_Top literally and preserves its old
headline as an explicitly LEGACY compatibility theorem. `CPH_CPS.correlated`
calls CPS_SourceTop.correlated directly on the derived game instance, also legacy
only. The adopted top reuses the CPP installation/protection and CPR history
route. Literal CPP_Endpoint is NOT invoked: its global-genesis, arbitrary lifetime
schedule and selected-writer experiment do not follow from pair fields(a)-(d).
Those extra hypotheses were not added to manufacture a literal call.

## Non-vacuity and next deliverable

`CPH_Nonvacuity.joint_runtime` jointly inhabits ALL new game/runtime conditions,
both exact runtime admissions, the approved SDK/std consistency models, BOTH
native wrappers evaluating inner Ok, nonempty physical events, exact copy/load
bytes and a constructed history. Account cells are nonaliased; all eight public
keys come from the retained accepted runtime pair. `CPH_FixtureFlags.privileges`
checks writable/nonsigner TX1 CP and readonly/nonsigner TX2 CP on the same key.

The local n1/n2 functions are explicit successful witnesses and proof/public
buffers are zero-filled model fixtures. **No extraction to the installed crypto
source is asserted.** `CPH_Nonrejecting.accepted_input` exports source acceptance
under retained P2Prime on the SAME source result; it does not construct P2Prime
or every other retained root hypothesis.

The independently retained actual native fixture succeeds for the exact default
ELF, both transactions and same CP. Static validation rechecks its receipts and
public-key association. Its candidate readonly-metadata LiteSVM feature, disabled
signature verification and synthetic registry limits remain explicit; it is not
joint kernel inhabitation of all retained hypotheses or certified deployed Agave.

The next deliverable is a full accepted fixture connecting actual native source,
retained Session A/source dictionaries, P2Prime/FirstEntry and frozen3
canonical/runtime binding on the SAME game instance. Repeating the local successful
stubs or the conditional accepted-input projection does not supply it. No source
refinement has been promoted to cryptographic or runtime trust.

## Validation, resources and freeze

All100 Lean invocations have exact target, command, source revision/hash,
selected direct object/sidecar dependency fingerprints, exit status, wall time,
peak RSS, swaps, enforced cgroup limits and complete #print axioms lines in
CPH_ATTEMPTS.jsonl and per-attempt receipts. Failed recovery sorryAx audits are
excluded. Final55 axiom lines contain only propext, Classical.choice and
Quot.sound (or none). Source/dependency changes motivated every rebuild; no
unchanged full regression or package replay ran.

Final root96: exit0, wall6.525543739960995s,
peakRSS5345156KiB, swaps0, revision23b37de9ce982cc25d5b3bb1d1942241761d1d79
plus exact source hash in receipt. Final audit101: exit0,
wall7.937414909014478s, peakRSS5318308KiB, swaps0,
revision688854c3ff8bd7ad66629d1a774bb4205f8b3ba1. Total measured Lean wall365.606231888989s;
maximum RSS5655548KiB, all swaps0.

Every scope used MemoryHigh6G/MemoryMax8G/MemorySwapMax0/TasksMax64 and Lean
-M7000, one admitted CPH scope at a time. Three vanished OTHER-worker cgroups
caused the specified30-second/single-retry barrier handling; no aggregate
reservation refusal, bypass or infrastructure edit occurred. One own missing
predecessor preflight24 launched no Lean. Normalization/namespace/elaboration
failures were isolated and repaired without raising depth/heartbeat/RAM caps.
No wall timeout, memory kill, Rust/Kani/SBF job or lingering CPH scope remains.

The final current core closure has31 own modules and129 source/object/sidecar
pins, zero variants and zero mismatches (CPH_HOST_PINS.json). Unchanged SInt2 and
historical native/core caches were reused. Inspect/FixtureTypes and the unused
reverse-projection Forget are retained auxiliary/historical audits, not the core
closure manifest. This is focused cached composition, not a new coherent frozen
release rebuild. The static CPH_validate.py audit passes for35 current module
source hashes,100 receipts,55 final axiom lines,1243 unchanged release input
files and the inherited runtime/artifact pins. git diff --check passes.

No shipped/cfg(kani) source, other prefix, session A worktree/candidate, feature,
wire format, lockfile, toolchain, ELF, wallet, key or funds changed. No SBF rebuild
trigger. No binary/object/ELF/archive committed. Inherited reproduced pins,
rechecked as evidence rather than newly rebuilt here:

- default f8c0ec72621fd5029a97d796c4a3623d0dc44a8e7074122372f9872915d143d4
- devnet 63ad3e9cc096dcbb55b3ca7ac7c8e89e6a845796ab5e4f5b7d15db96f3784299
- Pool 121f3e29741f510e6dc42d0345fc3c36217600f0be337094855c4a9da2581548

Stage commits:6e248d55af (inputs),91248a5b48 (source/game/protection),
6024a9beeb (recorded program/root compatibility),23b37de9ce (both traces and
actual-root source extraction),688854c3ff (recorder and receipt-key fixture).
The final evidence/handoff commit follows these; all commits remain local.
