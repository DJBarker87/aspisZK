import NNG_LegacyArrays136
import NNG_FromFnValues136
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNG_LegacyLow136
open Aeneas Aeneas.Std Result NNG_verify_finish NNG_Emitted NNG_Transport
open NNG_FromFnValues136 NNG_FromFnOn136
open NMT_Transport (arr)

theorem callback {H : Type} (d : AspisR1PublicPreparation.aspis_core.Digest32 H) (claims : Claims)
 (i : Usize) (bound : i.val<16) :
 (AspisR1PublicPreparation.FinishModel.closureFn9 d).call_mut (NNG_InstallClaims.lowerClaims claims) i=
 .ok (toT1 (firstValue claims i),NNG_InstallClaims.lowerClaims claims) := by
 change (do let row←Array.index_usize (arr (arr toT1) claims) 0#usize
            let q←Array.index_usize row i
            ok (q,NNG_InstallClaims.lowerClaims claims))=_
 rw [NNG_LegacyArrays136.index_map (arr toT1) claims 0#usize (by decide),bind_tc_ok]
 have selected := NNG_LegacyArrays136.index_map toT1 (NNG_Array136.get claims 0#usize (by decide)) i (by change i.val<29;omega)
 refine (congrArg (fun r : Result AspisR1PublicPreparation.aspis_core.field.QM31=>
   do let q←r;ok (q,NNG_InstallClaims.lowerClaims claims)) selected).trans ?_
 simp only [bind_tc_ok,firstValue,dif_pos bound]
 rfl

theorem array {H : Type} (d : AspisR1PublicPreparation.aspis_core.Digest32 H) (claims : Claims) :
 OraclePortStdBuilder.fromFn 16#usize (AspisR1PublicPreparation.FinishModel.closureFn9 d) (NNG_InstallClaims.lowerClaims claims)=
 .ok (arr toT1 (low claims)) := by
 obtain ⟨value,run,values⟩ := from_fn 16#usize (AspisR1PublicPreparation.FinishModel.closureFn9 d)
   (fun i=>toT1 (firstValue claims i)) (NNG_InstallClaims.lowerClaims claims)
   (by intro i hi;exact callback d claims i (indices_bound 16#usize i hi))
 have same : value=arr toT1 (low claims) := by
   apply Subtype.ext
   rw [values]
   change (OraclePortStdBuilder.indices 16#usize).map (fun i=>toT1 (firstValue claims i))=
     ((OraclePortStdBuilder.indices 16#usize).map (firstValue claims)).map toT1
   rw [List.map_map]
   rfl
 rw [same] at run
 exact run
#print axioms callback
#print axioms array
end AspisR1.NNG_LegacyLow136
