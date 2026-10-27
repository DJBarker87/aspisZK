import RPu_FJb_GroupIndices
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJb_MatrixBlock
open Aeneas Aeneas.Std Result FIq_Native
open FJb_MatrixGroupStep (State)
open FIv_NativeValue (K)
open FIw_ArrayValue (canonical decoded)
def block (state : State) (group : Usize) : Result State := do
  let start ← 4#usize * group
  let q ← Array.index_usize state start
  let i ← start + 1#usize
  let q1 ← Array.index_usize state i
  let i1 ← start + 2#usize
  let q2 ← Array.index_usize state i1
  let i2 ← start + 3#usize
  let q3 ← Array.index_usize state i2
  let input ←
    FIq_Native.core.array.Array.map (BuiltinFnMut field.QM31 (Array Std.U32 4#usize))
      (Array.make 4#usize [ q, q1, q2, q3 ])
      (state_only_poseidon.extension_limbs)
  let q4 ← state_only_poseidon.external_linear_lazy_row input 0#usize
  let state1 ← Array.update state start q4
  let q5 ← state_only_poseidon.external_linear_lazy_row input 1#usize
  let state2 ← Array.update state1 i q5
  let q6 ← state_only_poseidon.external_linear_lazy_row input 2#usize
  let state3 ← Array.update state2 i1 q6
  let q7 ← state_only_poseidon.external_linear_lazy_row input 3#usize
  Array.update state3 i2 q7

def input (s : State) (g : Nat) (k : Fin (4#usize).val) : K :=
  FIv_NativeArray.value s (4*g+k.val)
def model (s : State) (g : Nat) (j : Fin (16#usize).val) : K :=
  let rows := R0P.poseidonMat4 (input s g)
  if j.val=4*g+3 then rows 3 else
  if j.val=4*g+2 then rows 2 else
  if j.val=4*g+1 then rows 1 else
  if j.val=4*g then rows 0 else decoded s j

theorem factor (s : State) (g i0 i1 i2 i3 : Usize)
    (h0 : (4#usize*g : Result Usize)=ok i0)
    (h1 : (i0+1#usize : Result Usize)=ok i1)
    (h2 : (i0+2#usize : Result Usize)=ok i2)
    (h3 : (i0+3#usize : Result Usize)=ok i3) :
    block s g=FJb_MatrixGroupStep.step s i0 i1 i2 i3 := by
  simp only [block,FJb_MatrixGroupStep.step,h0,h1,h2,h3,bind_tc_ok]

#print axioms factor
end AspisR1.FJb_MatrixBlock
end
