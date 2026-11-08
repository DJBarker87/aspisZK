import NNX_C1Gather
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNX_Mask10
open Aeneas Aeneas.Std Result AspisR1PublicPreparation LIB_VCarriers
local instance : Inhabited aspis_core.field.QM31 := ⟨⟨⟨0#u32,0#u32⟩,⟨0#u32,0#u32⟩⟩⟩

theorem cell (c : Claims) (i : Usize) (bound : i.val < 10) :
 (LIB_VField.maskOnly c).val[i.val]! =
 LIB_VScalarCarriers.toRaw (LIB_VMask.cell c ⟨16+i.val,by omega⟩) := by
 have hi : i.val < (LIB_VField.maskOnly c).val.length := by
  rw [(LIB_VField.maskOnly c).property];exact bound
 rw [_root_.getElem!_pos (LIB_VField.maskOnly c).val i.val hi]
 simp only [LIB_VField.maskOnly,List.getElem_map,List.getElem_finRange]
 rfl

theorem closure {H : Type} (D : aspis_core.Digest32 H) (c : Claims) (i : Usize)
 (bound : i.val < 10) :
 (FinishModel.closureFn5 D).call_mut (claimsRaw c) i =
 .ok ((LIB_VField.maskOnly c).val[i.val]!,claimsRaw c) := by
 obtain ⟨j,add,hj⟩ := WP.spec_imp_exists
  (UScalar.add_spec (x:=16#usize) (y:=i) (by scalar_tac))
 have numeric : j.val = 16+i.val := hj
 have jb : j.val<29 := by omega
 have read := NNX_ClaimIndex.source c j jb
 change FinishModel.closureFn2 D (claimsRaw c) i = _
 unfold FinishModel.closureFn2
 rw [add,bind_tc_ok]
 have mapped := congrArg (fun result : Result aspis_core.field.QM31 => do
  let value ← result
  .ok (value,claimsRaw c)) read
 have normalized := mapped
 simp only [bind_assoc_eq,bind_tc_ok] at normalized
 rw [cell c i bound]
 have same : (⟨j.val,jb⟩ : Fin 29) = ⟨16+i.val,by omega⟩ := Fin.ext numeric
 rw [same] at normalized
 exact normalized

theorem source {H : Type} (D : aspis_core.Digest32 H) (c : Claims) :
 OraclePortStdBuilder.fromFn 10#usize (FinishModel.closureFn5 D) (claimsRaw c) =
 .ok (LIB_VField.maskOnly c) := by
 apply NNX_Gather.array
 intro i inside
 exact closure D c i (NNX_C1Gather.member 10#usize i inside)
#print axioms cell
#print axioms closure
#print axioms source
end AspisR1.NNX_Mask10
end
