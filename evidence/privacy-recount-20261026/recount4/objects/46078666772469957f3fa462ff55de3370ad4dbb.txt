import R1Z.ProverRwSuccessHashes
set_option autoImplicit false
noncomputable section
open Aeneas Aeneas.Std Result ControlFlow Error ProverRwFull
namespace R1Z.ProverRwSuccessPhiSource
def generic54.phi_inverse
  {E : Type} (scalarCodeFieldInst : aspis_core.r0.scalar.CodeField E) (x : E) (y : E)
  (h : Array E 4#usize) :
  Result (Array E 4#usize)
  := do
  let h0 ← Array.index_usize h 0#usize
  let h1 ← Array.index_usize h 1#usize
  let h2 ← Array.index_usize h 2#usize
  let h3 ← Array.index_usize h 3#usize
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
end R1Z.ProverRwSuccessPhiSource
