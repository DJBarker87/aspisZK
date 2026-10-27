# Symbolic finalizer mathematics

LPe_MersenneReduction.fold_mod proves the 31-bit fold preserves residue mod
2147483647 for every natural input. fold_twice_lt proves two folds are below
2P for every n<2^64. reduce_eq_mod proves the two folds and one conditional
subtraction equal n%P throughout that domain. zero_witness gives nonemptiness.

L001 failed on an unreduced let before split_ifs. Its automatic error-recovery
sorryAx output is NOT accepted evidence. L002 changes unfold to dsimp, passes
all four statements and prints every axiom report: fold_mod [propext], bounds
and reduce_eq_mod [propext, Quot.sound], zero_witness no axioms.
No source sorry/admit/axiom/native_decide or option cap override appears.

Native K013 proves private canonical::Dot::finish returns the explicit WORD
reduction on arbitrary u64 sums. L002 supplies the natural-number arithmetic
fact for that reduction shape; the Rust bitwise/word-to-natural refinement,
reached sum invariant, public EbyKDot::finish wrapper and P6/model composition
are NOT silently supplied. No caller or actual-top premise is discharged.

One changed module at a time, reused coherent Mathlib objects, pinned Lean4.32,
-M7000 and6G/8G/swap0/tasks64. L002 exit0,0.751356495s,1542508KiB RSS,swap0;
source revision and exact source/dependency/tool hashes are in its receipt.
No unchanged full regression or package replay. No extra wrapper theorem is
introduced to hide the remaining native bridge. Native allowance20/20 is
exhausted; Lean allowance2/60 is used, not described as exhausted.
