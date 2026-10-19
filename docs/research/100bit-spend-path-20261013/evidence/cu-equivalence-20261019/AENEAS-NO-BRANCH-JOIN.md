The private no-branch-join frontend is an opt-in workaround for the pinned
interpreter's nested-shared-reference context-merge failure on View.query.
It retains the initial Unit-result invariant and returns the same unmerged
branch contexts and continuation already used by the interpreter's existing
merge fallback. No borrow, translation, arithmetic or type check is removed.
The exact three-line patch is aeneas-no-branch-join.patch; base/source hashes
are in aeneas-no-branch-join-pins.json. No proof body or production Rust changes.

Pinned base: b59d5188c082f704a418c7cb4e52ad69328002d1.
Experimental binary SHA-256:
f4303c70b54b9b64d9475a736d2193eafd557005262fabdb7f31953a98f62122.
Build receipt: aeneas-no-branch-join-build/receipt.json. The independent copied
source/cache was rebuilt with optimized Dune, one job, actual 6/8 GiB Docker
memory high/max and zero permitted swap. Build wall 6.760 s, peak RSS
502548 KiB, process/cgroup swap zero. Pinned original sources/binary untouched.

The actual View.query emission uses AENEAS_DISABLE_BRANCH_JOIN=1, the same
Charon LLBC as the failing original emission, and the selected production
private-leaf-salts configuration. cu-query-aeneas-b records the complete
command, revision/features, hashes, exit 0, wall 0.401 s, peak RSS 71984 KiB,
process/cgroup swap zero. No axiom template is admitted by its checked query
proofs. All generated declarations are promoted unchanged.

Paired regression nojoin-regression-a compares against archived baseline
emission hashes (no unchanged baseline rerun). Flag off: prefix, initialization
row, iterator emit byte-identical Types/Funs. Flag on: prefix emits identical
Types/Funs. All four pass. Per-case commands, input/output hashes, revision,
features, exit, wall, RSS and swaps are in nojoin-regression-emission-a;
parent scope/resource receipt is in nojoin-regression-a. Parent wall 1.203 s,
peak 75328 KiB, zero process/cgroup swap. #print axioms is inapplicable to
frontend byte comparisons; consuming Lean results have their own axioms audits.

This regression supports the narrow workaround; it is not a proof of compiler
correctness or general branch-join equivalence. The trusted frontend boundary
is explicit. All final source-equivalence and soundness/privacy claims still
require the consuming caller and whole-verifier composition obligations.
