# ARR stage 2: reached-return characterization and exact prefix cost

ARR_ReturnCoverage.iff_returns (042) proves, under the retained returning-value
compatibility law, that Covered is equivalent to EVERY actual attempted syscall
returning successfully. This does not require the source execution itself to
succeed: pure source errors, divergence steps and early exits are included.
Its of_returns and returns_of_covered directions are independently audited.

ARR_PrefixCost.suffix (043) uses the actual RPx_AttemptPrefix.transport and proves
ideal addresses = every native attempted address ++ remaining; ideal issued
count = native attempted count + remaining.length. It retains the failed syscall's
address. native_le_ideal and same_cost_iff_empty expose the exact work loss;
an upper bound is not silently promoted to original-cost equality.

All six new theorem audits are [propext, Classical.choice, Quot.sound].
Target042 exit0 wall2.6305759889655747s RSS5289020KiB swap0.
Target043 exit0 wall2.2329674909706227s RSS5290016KiB swap0.
Exact revisions, source snapshots/hashes, commands, dependency object hashes and
scope limits are in their canonical receipts. These are source/interface results,
not a coherent release replay or native bank coverage proof.

Missing unchanged dependencies compiled, one scope at a time:
013-020 and022-041, all passing, no source edit to those modules. Their committed
receipt snapshots are exact copies of existing repository sources; no .olean is
committed. 021 attempted the bank/choice-padding module but could not load the
same missing Port1_CanonicalHeadline dependency. That draft remains unaccepted.

42 actual Lean invocations through043: 33 pass,9 excluded failures;002 is a
prelaunch prerequisite failure, not a compiler invocation. 0 Kani. No resource
kill, timeout, raised cap or unchanged compiler-failure rerun. 001->005 changed
the module imports; their identical missing dependency errors are retained.

No actual-top premise removed. The intended ARR_Coverage/ARR_Carrier and concrete
native-account drafts have not been checked, and are not accepted proof artifacts.
The fixed-hash compatibility finding alone does NOT prove an allowed deployed
execution is excluded: the corresponding account acceptance/bank association
must also be proved. That whole-game classification remains open.
