# Runtime persistence handoff

**Target not yet established. Actual deployed L094/L095/L096/L180 delta: ZERO.**
Branch `codex/cx-cp-runtime-20261026`; no push. Decision packet:
`design/RUNTIME-PERSISTENCE-ITEM-20261026.md`.

## Established and remaining claims

Existing RuntimeEntrypointAdmission, RuntimeSyscall, Allocator and S2W extraction
records do not state a bank commit/rollback/load law. CheckpointVersionBinding
already contains the desired history fields and cannot discharge itself.
`CPR_Separation.independent` and `CPR_DataGap.old_items_do_not_supply_data_loader`
are checked conservative-extension countermodels. The exact existing record
statements are printed in CPR_L024. No runtime trust was adopted.

The narrow proposal is `CPR_DataPersistence.TwoTransactionLaw`: on a consecutive
physical account load, ordinary accounts expose the final successful parent's
data, or the pre-parent data on failure, with zero lamports observed as absence.
It asserts no whole execution, next owner/balance, acceptance or source-event
equality. Fee payer / durable nonce exceptions are excluded explicitly. Official
Solana pipeline documentation and read-only pinned Agave v3.1.13 references are
cited in the decision packet; they are NOT a deployed validator/feature pin.
The stronger earlier full-image formulation is retained, with a checked strict
separation in CPR_DataGap.narrow_holds/full_fails.

`CPR_PhysicalTop.deployed` composes the ACTUAL T2R_Top.deployed, retaining its
headline Claims/bounds, c, entries, input bytes and SAME f,s,run,tx2 witnesses.
It returns CPR_PhysicalResult.Outcome, constructs all three version fields,
removes the history arguments from the acceptance and caller continuations,
and exposes version.events = physicalEvents t. P2Prime and FirstEntry remain.
`CPR_PhysicalOrder.original` returns the original FullResult on identical
witnesses. CPR_BEFORE/AFTER files and CPR_L024 retain exact source/elaborated
statements; CPR_LEDGER_DELTA.json records zero actual removal.

This is CONDITIONAL source/model progress. Besides the proposed law it retains
explicit pure-key/source-entry, complete parent-final image, physical pairing,
status, ordinary-key eligibility, reader-buffer and ordered-event interpretations.
The branch covers a positive-balance writer and adjacent successful writer
parent/reader pair. The balance-aware TX1 entry uses the SAME initial bank
lamports. No independently chosen successful source cuts or desired history are
hypotheses, but the physical/source interpretations remain uninstantiated.
`eventsView` is precisely a local source-refinement obligation, NOT new trust.
Calling an arbitrary projection `physicalEvents` does not certify its deployment.

The requested **single-law-only L180 closure is NOT established**. The checked
CPR_KeyGap model has a true runtime law but no history across independent keys.
CPR_EventsGap has unchanged final bytes and a true byte law but no protected
history for its specified key/events. Endpoint-image equality therefore cannot
replace source-event association. These are interface/history-algebra models,
NOT counterexamples to all original accepted crypto/native premises and NOT
shipped-source security findings. CPR_AdmissionGap separately inhabits the full
SDK mathematical model and both exact admission records with equal key metadata
and CP lengths but unequal buffers; native acceptance is not asserted.

Local non-vacuity: CPR_Nonvacuity covers a nonempty credit/foreign-write/cleanup
suffix, positive protected-key survival, canonical runtime-law models and parent
rollback of tentative writes and credits. No joint accepted crypto/native/bank
inhabitant or ordered runtime failure-mass transport is claimed.

Next deliverable: concrete bank/executor source-event and input/candidate/load
interpretation, then physical-lifetime-aware writer selection handling temporary
zero-funded CPs, cleanup/recreation and failed parents. Supply actual validator /
feature / source-to-ELF correspondence before adopting a runtime law or claiming
the four ledger rows removed. The CPP endpoint was NOT adopted into the root.

## Validation and resources

25/100 Lean invocations, including all dependencies (none missing); 21 pass,
4 development failures. 0/10 Kani; no Rust/SBF/package/frozen-manifest replay.
Every job used one existing runner in the coherent SInt2 workspace, -M7000,
MemoryHigh=6G, MemoryMax=8G, MemorySwapMax=0, TasksMax=64 and the existing
reservation barrier. All admissions passed; no retry, timeout, memory kill,
cap increase or unchanged full regression occurred. No CPR scope remains.

Failed attempts: L003 reserved identifier `protected`; L006 ambiguous `put`;
L012 tiny decide needed its concrete Nat goal exposed; L015 rewrite needed
explicit beta-reduced target. Corrected sources passed L004/L007/L013/L016.
Failed parser/elaborator receipts can contain sorryAx recovery output and are
EXCLUDED; every delivered proof has a successful exact-source receipt and
standard axioms only. All failed source snapshots/logs are retained.

L024 target CPR_Statements.lean, exit0, wall2.42293207696639s,
peakRSS5265360KiB,swap0; source revision
9eeaf35832d4208895a8351b12aab41bfa362e16 plus exact dirty source SHA
 deefea70493f1cbd7ebdb79cc64445561fe0da0c024398aa548858f2513ed687.
Its44 printed axiom lines include the original deployed root. L025 independently
audits the later event counterexample: exit0,wall2.489440200966783s,
peakRSS5251300KiB,swap0. Only propext, Classical.choice and Quot.sound occur in
accepted proofs (some use fewer or none). Per-attempt receipts contain exact
commands, targets, source revisions/hashes, dependency fingerprints, exit,
wall/RSS/swap, cgroup limits and full axiom lines.

Total Lean wall52.82466678094352s; maximumRSS5359984KiB; every swap0.
CPR_validate.py is a read-only receipt/source/axiom checker, never a launcher or
monitor. CPR_VALIDATION.json checks all21 current modules. CPR_HOST_PINS.json
pins89 current host source/object/sidecar inputs, matching local sources and all
selected direct objects. The coherent CPP/Hist/Hiq/Hir/SInt2 objects and pinned
historical closure were reused; this is focused cached composition, not a full
frozen-release rebuild. Proof/design whitespace checks pass.

Budget is NOT exhausted: 75 Lean /10 Kani remain unused. The law-only inference
was stopped under r1p-common rule4 after checked pairing/event countermodels;
the remaining source association cannot be inferred by repeating that false
interface implication. No budget exhaustion or full task completion is claimed.

## Freeze

No shipped file, cfg(kani) harness, lock, feature, wallet, key, account or funds
changed. No binary/object/ELF/archive committed. No local target directory or
wallet cleanup. Only CPR_ modules, this job's evidence and the requested design
file changed. Session A and other workers' worktrees/candidates were untouched.
No ELF rebuild trigger. Inherited pins, NOT reproduced by this job:

- default f8c0ec72621fd5029a97d796c4a3623d0dc44a8e7074122372f9872915d143d4
- devnet 63ad3e9cc096dcbb55b3ca7ac7c8e89e6a845796ab5e4f5b7d15db96f3784299
- Pool 121f3e29741f510e6dc42d0345fc3c36217600f0be337094855c4a9da2581548

Stage commits before final audit/handoff: 89a18ebc0b,17bf66fff6,9eeaf35832.
All commits remain local. The 100-bit release target remains NOT ESTABLISHED.
