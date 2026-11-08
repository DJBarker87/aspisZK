import NNX_ClaimIndex
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNX_Mask16
open Aeneas Aeneas.Std Result AspisR1PublicPreparation LIB_VCarriers
local instance : Inhabited aspis_core.field.QM31 := ⟨⟨⟨0#u32,0#u32⟩,⟨0#u32,0#u32⟩⟩⟩

theorem member (n i : Usize) (inside : i ∈ OraclePortStdBuilder.indices n) : i.val < n.val := by
 unfold OraclePortStdBuilder.indices at inside
 obtain ⟨j,hj⟩ := List.mem_ofFn.mp inside
 rw [←hj]
 exact j.isLt

theorem cell (c : Claims) (i : Usize) (bound : i.val < 16) :
 (LIB_VField.c1 c).val[i.val]! =
 LIB_VScalarCarriers.toRaw (LIB_VMask.cell c ⟨i.val,by omega⟩) := by
 have hi : i.val < (LIB_VField.c1 c).val.length := by rw [(LIB_VField.c1 c).property];exact bound
 change ((LIB_VField.c1 c).val[i.val]?).getD default = _
 rw [List.getElem?_eq_getElem hi]
 simp only [Option.getD_some,LIB_VField.c1,List.getElem_map,List.getElem_finRange]

theorem closure {H : Type} (D : aspis_core.Digest32 H) (c : Claims) (i : Usize)
 (bound : i.val < 16) :
 (FinishModel.closureFn9 D).call_mut (claimsRaw c) i =
 .ok ((LIB_VField.c1 c).val[i.val]!,claimsRaw c) := by
 have read := NNX_ClaimIndex.source c i (by omega)
 have mapped := congrArg (fun result : Result aspis_core.field.QM31 => do
  let value ← result
  .ok (value,claimsRaw c)) read
 simpa only [FinishModel.closureFn9,FinishModel.closureFn6,bind_assoc_eq,bind_tc_ok,cell c i bound] using mapped

theorem source {H : Type} (D : aspis_core.Digest32 H) (c : Claims) :
 OraclePortStdBuilder.fromFn 16#usize (FinishModel.closureFn9 D) (claimsRaw c) =
 .ok (LIB_VField.c1 c) := by
 apply NNX_Gather.array
 intro i inside
 exact closure D c i (member 16#usize i inside)
#print axioms member
#print axioms cell
#print axioms closure
#print axioms source
end AspisR1.NNX_Mask16
end
