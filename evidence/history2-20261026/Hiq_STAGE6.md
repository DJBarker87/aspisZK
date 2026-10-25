# Stage 6: actual release dispatcher and Pool source metadata guards

Actual unmodified pinned source was extracted with optimized Charon then Aeneas.
Hiq_DispatchRelease.source checks the COMPLETE emitted release filter/dispatcher:
TX1 [3,10]/[3,11], arbitrary-length ASQ8, all legacy/lifecycle rejection paths,
selected native child return, child errors and divergence. lifecycle_irrelevant
proves excluded lifecycle callbacks cannot affect a release result. No successful
child call is a premise. Hiq_DispatchOracle retains the selected child's entire
ordered log and proves all rejected dispatcher inputs make zero oracle queries.
Native child/SDK state effects are still separate, not derived by parametric
AccountInfo abstraction. The dispatcher never inspects AccountInfo fields.

Source bodies retain branch/order/error values, with external templates replaced
by explicit typed callbacks and documented pure slice/U8/Option library semantics.
Source snapshots, raw emission, adaptation/source hashes and resource receipts
are retained. No new axioms or resource overrides. This is source control-flow
refinement, not a claim of complete native child or runtime refinement.

Pool Charon002 succeeded, but Aeneas002 FAILED with internal Unreachable in
SymbolicToPureValues.ml:878 at pair_forest.rs:400-415 require_program_owned_zeroed.
No source counterexample follows. No translator/launcher repair, unchanged retry
or cap increase. Isolated metadata-only Charon003/Aeneas003 succeeded.
Hiq_PoolGuards.account_iff/owned_iff prove the actual Pool source owner,
executable, writable guards under the documented pure key comparison, using
canonical SDK metadata projections. The borrowed zero/fresh gates and COMPLETE
Pool immutable checkpoint writer/lifecycle remain unproved. No L180 closure.

Hiq_CanonicalCarrier constructs the logical/physical Input from source bytes
using the canonical Port1 carrier rather than a chosen logical proof or tag.
Hiq_StoredTransport proves probability transport with one explicit same-world
bad event. It leaves the whole-run equality outside bad EXPLICIT: it does not
close L159 by renaming that assumption. Hiq_MeanSum proves the shared-oracle
three-program expectation inequality via finite support, without independence.

Global ledger delta: removed NONE; no claim that bytes/acceptance alone give
ordered run/logical-proof equality. All original release/security targets remain.
Budget through60:60 charged Lean submissions (59 actual plus prelaunch022),
0 Kani;3 optimized Charon and3 Aeneas jobs (one excluded translator failure).
All accepted Lean top theorems print only standard axioms. No timeout/memory
kill or raised limits. Full exact receipts retained. No shipped source, harness,
keys, accounts, artifacts, other worker sources or launchers changed. No ELF
rebuild trigger and no package replay. Pins remain inherited, not rebuilt.
