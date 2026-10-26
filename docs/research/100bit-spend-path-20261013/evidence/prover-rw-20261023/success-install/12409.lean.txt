import R1Z.ProverRwSuccessGeneric
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverRwSuccessPhiReads
open Aeneas Aeneas.Std Result ProverRwFull

def formula {E : Type} (scalarCodeFieldInst : aspis_core.r0.scalar.CodeField E)
    (x y h0 h1 h2 h3 : E) : Result (Array E 4#usize) := do
  let a ← scalarCodeFieldInst.mul y h1
  let b ← scalarCodeFieldInst.mul x h2
  let t ← scalarCodeFieldInst.mul x y
  let c ← scalarCodeFieldInst.mul t h3
  let t1 ← scalarCodeFieldInst.add h0 a
  let t2 ← scalarCodeFieldInst.add t1 b
  let t3 ← scalarCodeFieldInst.add t2 c
  let t4 ← scalarCodeFieldInst.sub h0 a
  let t5 ← scalarCodeFieldInst.add t4 b
  let t6 ← scalarCodeFieldInst.sub t5 c
  let t7 ← scalarCodeFieldInst.sub t4 b
  let t8 ← scalarCodeFieldInst.add t7 c
  let t9 ← scalarCodeFieldInst.sub t1 b
  let t10 ← scalarCodeFieldInst.sub t9 c
  ok (Array.make 4#usize [ t3, t6, t8, t10 ])

variable [ExternalTypes]
theorem reads_total (ops : ExternalFuns) {E : Type}
    (inst : aspis_core.r0.scalar.CodeField E) (x y : E) (h : Nat → E) :
    (ProverRwSuccessGeneric.selected ops).op80 inst x y (ProverCommitArray49.array 4#usize h) =
      formula inst x y (h 0) (h 1) (h 2) (h 3) := by
  change ProverRwSuccessPhiSource.generic54.phi_inverse inst x y _ = _
  simp only [ProverRwSuccessPhiSource.generic54.phi_inverse,
    ProverCommitArray49.index 4#usize h 0#usize (by decide),
    ProverCommitArray49.index 4#usize h 1#usize (by decide),
    ProverCommitArray49.index 4#usize h 2#usize (by decide),
    ProverCommitArray49.index 4#usize h 3#usize (by decide),bind_tc_ok]
  rfl
#print axioms reads_total
end R1Z.ProverRwSuccessPhiReads
