# Stage 3 — annotation backward law and final handoff

`Port1_Annotation.source_enrich` proves equality of the complete source oracle
program under enrichment, and `backward` is exactly the one-way acceptance
law consumed by `VTop_Annotation.two_pass`, instantiated at the named
`Port1_Driver.rust`. No raw join, model-order identity, decoder correctness,
body correctness or source verdict-stability premise is needed for this local
law: enrichment preserves the physical public/stored arguments. It follows
for every body/decoder dictionary and every oracle. This closes the requested
source backward law for that constructed lift, independently of stage2.

No complete AcceptedRunJoin theorem is asserted by assuming an impossible
nontrivial unrestricted raw join. The stage2 carrier theorem explains that
remaining issue. The eventual deployed source/runtime binding, logical carrier
transport, same-state body refinements and frozen2 model order are still open.
The source/public decoder is the actual adapter cut, not a proved new concrete
S6 instance; session A's decoder/backends/artifact obligations are retained.

Final focused audit `Port1_Audit.lean`, lean012: exit0, wall2.005180901s,
peak RSS4312040KiB, swap0; prints all21 added theorem audits and the exact
TrustedStd/BodyJoins/backward interfaces. Only subsets of propext,
Classical.choice, Quot.sound appear. Source revision dbbd073015 plus the exact
new source hashes and imported object fingerprints is pinned in its receipt.
This is a compatible focused import audit, not a coherent frozen manifest or
release replay. No new full replay is appropriate while the closure is open.

Budget: **11/100 actual Lean compiles, 0/60 Kani runs**;12 IDs allocated,
including compiler-free preflight002.8 final accepted modules;3 elaboration
failures retained and excluded (004,005,007). Total compiler-command wall
22.554893344s; maximum process RSS4342384KiB; every recorded swap count0.
All compiles: exact target module via lake env lean -j1 -M4400
-DElab.async=false, Linux host, shared global lock, private object directory,
MemoryHigh6G/MemoryMax8G/MemorySwapMax0/TasksMax64 and reservation admission.
No memory kill, wall timeout, unchanged rerun, cap increase, Rust or Kani job.
The final host query found no running Lean process; all worker jobs are terminal.

Port-table update is in design/VERIFIER-TOP-20261023.md: library semantics and
source annotation backward acceptance closed for the installed interpretation;
source driver/same-checkpoint substitution advanced; actual frozen2 raw/model
binding remains explicitly OPEN at the checked carrier obstruction.

No shipped file (including cfg(kani) harnesses), existing Lean module, other
worker's source/candidate/worktree, key, parameter or security contract changed.
Git diff against d40009ca879ba82276384f7e97df44fb25e998d2 is empty for crates,
programs and Cargo inputs. Three-ELF rebuild trigger did not fire. Existing pins
remain default f8c0ec72621fd5029a97d796c4a3623d0dc44a8e7074122372f9872915d143d4,
devnet63ad3e9cc096dcbb55b3ca7ac7c8e89e6a845796ab5e4f5b7d15db96f3784299,
Pool121f3e29…; no independent new rebuild/reconfirmation is claimed.

Run the compiler-free packet audit with:
`python3 tools/ports1-20261023/Port1_audit.py`.
All receipt hashes, final-source accepted coverage, allowed axioms, retained
source bodies and source constant equations pass. The actual deployed
soundness target is **not yet established**. Next deliverable: source-indexed
logical carrier construction and proved accepted-experiment transport, then
same-state per-body instances and the frozen2 query/flush/batch1 order proof.
All commits remain local; nothing pushed.
