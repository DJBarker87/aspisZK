# P6B stage 2: checked runtime obstruction

Established: P6B_Totality.wrapper_total_iff and installed_total_iff prove,
under exactly the existing P1 and RuntimeSyscall, that the total digest law
is equivalent to Returns hashv = forall parts, exists value, hashv parts = ok value.
The installed theorem uses D188.digestSource on the same ops/native1/native2.
It adds no SDK success, caller fact, Merkle equality or log assumption.

P6B_Totality.nonvacuity constructs P1 H H and RuntimeSyscall (partialHash H) H,
a successful empty-parts call, and failure of Returns. Nonempty queries
nonreturn in this interface model. This is NOT a shipped runtime execution,
SDK defect or counterexample to the full accepted spend theorem. It proves
that the existing value-only law does not entail the missing return law,
even when successful calls exist. The failure/divergence-preserving wrapper
cannot prove that law by source arithmetic. Host SHA256's implementation is
irrelevant to the deployed syscall branch.

STOP CONDITION REACHED: total VM normal return on every Parts input is a
runtime trust/termination obligation beyond the adopted RuntimeSyscall, not
pure source behaviour. No such trust item is adopted here. Blanket all-input
normal return should not be added without checking VM abort/resource/domain
semantics. A narrower reached/admitted-call proof or accepted-run interface
would require a separately justified transport, not silent weakening of L195.
Per the explicit instruction "then stop and report", no artificial budget
exhaustion or further Kani/Lean runs follow this obstruction.

P6B_001 is EXCLUDED: exit1, wall4.123585135s, peak4343976KiB, swap0;
one local simp failed to reduce if True. Its recovery sorryAx printouts give
NO proof credit. P6B_002 source-changes that step to ite_true: exit0,
wall5.847740322s, peak4362528KiB, swap0. Every one of its six printed theorem
audits is [propext, Classical.choice, Quot.sound]. Exact revision/hash,
dependency objects, command and cgroup fields are in each receipt.
Both use lake env lean -j1 -M7000 -DElab.async=false,6G high/8G max/swap0/64 tasks.
No timeout/memory kill or unchanged rerun occurred. One scope at a time.

Admission001 initially refused at64827162624 reserved bytes. Retried after
215.98 seconds, allowed at43352326144 bytes (+8GiB below55GiB).
No compile started on the refusal. Existing SInt2 host/cache and unchanged
S2W runners reused; no infrastructure modified and no dependency builds.
Budget:2/100 Lean attempts,0/20 Kani. No release/package/SBF replay.
