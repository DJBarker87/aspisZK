import FJb_MatrixGroupStep
import FJb_ColumnIndices
import FJb_LimbMap
import RawPoseidonExternalRowReads
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJb_ColumnCell
open Aeneas Aeneas.Std Result FIq_Native
open FIv_NativeArithmetic (NQ)
open FJb_MatrixGroupStep (State)
def word (q : NQ) (limb : Usize) (hi : limb.val < (4#usize).val) : U32 :=
  (FJb_LimbMap.words q).val[limb.val]'(by simpa only [(FJb_LimbMap.words q).property] using hi)
def atWord (s : State) (n : Nat) (limb : Usize) (hi : limb.val < (4#usize).val) : U32 :=
  if h : n < (16#usize).val then word (FIw_ArrayValue.cells s ⟨n,h⟩) limb hi else 0#u32
abbrev call := state_only_poseidon.external_linear_lazy.closure.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU64.call_mut
/-- The SAME four source cells feed the exact native column-limb sum. -/
theorem value (s : State) (c limb : Usize) (hc : c.val < 4) (hi : limb.val < (4#usize).val) :
    ∃ out,call (s,c) limb=ok (out,(s,c)) ∧
      out.val=(atWord s c.val limb hi).val+(atWord s (4+c.val) limb hi).val+
        (atWord s (8+c.val) limb hi).val+(atWord s (12+c.val) limb hi).val ∧
      out.val < 2^34 := by
  obtain ⟨i1,i2,i3,r1,v1,r2,v2,r3,v3⟩ := FJb_ColumnIndices.value c hc
  have b0 : c.val < (16#usize).val := by change c.val < 16;omega
  have b1 : i1.val < (16#usize).val := by change i1.val < 16;omega
  have b2 : i2.val < (16#usize).val := by change i2.val < 16;omega
  have b3 : i3.val < (16#usize).val := by change i3.val < 16;omega
  let q0 := FIw_ArrayValue.cells s ⟨c.val,b0⟩
  let q1 := FIw_ArrayValue.cells s ⟨i1.val,b1⟩
  let q2 := FIw_ArrayValue.cells s ⟨i2.val,b2⟩
  let q3 := FIw_ArrayValue.cells s ⟨i3.val,b3⟩
  have h0 : Array.index_usize s c=ok q0 := RawPoseidonExternalRowReads.array_index_usize_ok s c b0
  have h1 : Array.index_usize s i1=ok q1 := RawPoseidonExternalRowReads.array_index_usize_ok s i1 b1
  have h2 : Array.index_usize s i2=ok q2 := RawPoseidonExternalRowReads.array_index_usize_ok s i2 b2
  have h3 : Array.index_usize s i3=ok q3 := RawPoseidonExternalRowReads.array_index_usize_ok s i3 b3
  have e0 : state_only_poseidon.extension_limbs q0=ok (FJb_LimbMap.words q0) := rfl
  have e1 : state_only_poseidon.extension_limbs q1=ok (FJb_LimbMap.words q1) := rfl
  have e2 : state_only_poseidon.extension_limbs q2=ok (FJb_LimbMap.words q2) := rfl
  have e3 : state_only_poseidon.extension_limbs q3=ok (FJb_LimbMap.words q3) := rfl
  have l0 : Array.index_usize (FJb_LimbMap.words q0) limb=ok (word q0 limb hi) :=
    RawPoseidonExternalRowReads.array_index_usize_ok _ limb hi
  have l1 : Array.index_usize (FJb_LimbMap.words q1) limb=ok (word q1 limb hi) :=
    RawPoseidonExternalRowReads.array_index_usize_ok _ limb hi
  have l2 : Array.index_usize (FJb_LimbMap.words q2) limb=ok (word q2 limb hi) :=
    RawPoseidonExternalRowReads.array_index_usize_ok _ limb hi
  have l3 : Array.index_usize (FJb_LimbMap.words q3) limb=ok (word q3 limb hi) :=
    RawPoseidonExternalRowReads.array_index_usize_ok _ limb hi
  obtain ⟨out,hr,hv,hb⟩ := FJb_WideSum4.value
    (word q0 limb hi) (word q1 limb hi) (word q2 limb hi) (word q3 limb hi)
  refine ⟨out,?_,?_,hb⟩
  · dsimp only [call,state_only_poseidon.external_linear_lazy.closure.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU64.call_mut]
    simp only [h0,e0,l0,r1,h1,e1,l1,r2,h2,e2,l2,r3,h3,e3,l3,lift,bind_tc_ok]
    have hcall : (do
      let x ← FJb_WideSum4.source (word q0 limb hi) (word q1 limb hi) (word q2 limb hi) (word q3 limb hi)
      ok (x,(s,c)))=ok (out,(s,c)) := by rw [hr,bind_tc_ok]
    simpa only [FJb_WideSum4.source,FJb_WideSum4.wide,bind_assoc_eq] using hcall
  · have b1' : 4+c.val < (16#usize).val := by omega
    have b2' : 8+c.val < (16#usize).val := by omega
    have b3' : 12+c.val < (16#usize).val := by omega
    simpa only [atWord,dif_pos b0,dif_pos b1',dif_pos b2',dif_pos b3',
      q0,q1,q2,q3,v1,v2,v3] using hv
#print axioms value
end AspisR1.FJb_ColumnCell
end
