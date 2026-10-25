# Retained carrier countermodel

The requested op5 closure is not established. The checked new result is an
observation-contract countermodel, not a shipped-source counterexample.
`Op5I_EventCounterexample.inject` preserves every original invocation's
Result value, failure and divergence, while adding any supplied child event
to each returning invocation. `first_marks` and `second_marks` prove that
both original source mark contracts survive this change. Nothing in this
construction modifies Ops, native1/native2, hashv or AeneasExtraction.

Before: ChildConeJoin.erasure plus FirstMarks/SecondMarks constrain source
values and mark layout. After: the SAME contracts are satisfied after adding
an arbitrary event. Thus they do not by themselves fix an oracle-event
interpretation. The next stage must connect this countermodel to the SAME
accepted_pair_claims witnesses and exhibit an oracle-inconsistent read.
No new security assumption or source-adoption boundary is introduced.

Host: approved coherent codex-cx-sound-int2-20261025 workspace, unchanged
S2W launchers and cached objects. Each target used lake env lean -j1 -M7000
-DElab.async=false in MemoryHigh=6G/MemoryMax=8G/MemorySwapMax=0/TasksMax=64.
Preflight systemctl reported no populated build scope. No dependency build,
Kani/Rust/SBF job, package replay or release replay occurred.

Op5I-001 failed elaboration (bind simplification and redundant tactics);
its recovery axioms are excluded. Source changed before Op5I-002 passed:
exit0, 2.11907296202844 seconds, peak5141728 KiB, swap0, source revision
4dfb9dccec5ce1289c8cabe88b125e6378fd5aea (dirty new module). All four
new top theorem audits contain only propext, Classical.choice, Quot.sound.
Each attempt directory records exact target/command, source hash/snapshot,
direct object fingerprints, exit/wall/RSS/swap/cgroup and full axioms/errors.

Budget2/60 Lean,0/20 Kani. Only Op5I_ new modules and this receipt directory
changed. No existing proved module, shipped file, key or other worktree changed.
No ELF rebuild trigger; release pins remain inherited and unverified here.
