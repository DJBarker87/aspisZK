import NNG_LegacyLow136
import NNG_Offset16
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNG_LegacyHigh136
open Aeneas Aeneas.Std Result NNG_verify_finish NNG_Emitted NNG_Transport
open NNG_FromFnValues136 NNG_FromFnOn136 NNG_Offset16
open NMT_Transport (arr)

theorem add_shift (i : Usize) (bound : i.val<10) : (16#usize+i : Result Usize)=.ok (shifted i) := by
 have big : (29 : Nat)≤Usize.max := by
   have h := (29#usize).hmax
   scalar_tac
 have safe : (16#usize).val+i.val≤Usize.max := by change 16+i.val≤_;omega
 obtain ⟨v,run,val⟩ := WP.spec_imp_exists (Usize.add_spec (x:=16#usize) (y:=i) safe)
 have same : v=shifted i := UScalar.eq_of_val_eq (val.trans (NNG_Offset16.value i bound).symm)
 rw [same] at run
 exact run

theorem callback {H : Type} (d : AspisR1PublicPreparation.aspis_core.Digest32 H) (claims : Claims)
 (i : Usize) (bound : i.val<10) :
 (AspisR1PublicPreparation.FinishModel.closureFn5 d).call_mut (NNG_InstallClaims.lowerClaims claims) i=
 .ok (toT1 (secondValue claims i),NNG_InstallClaims.lowerClaims claims) := by
 change (do let j←(16#usize+i : Result Usize)
            let row←Array.index_usize (arr (arr toT1) claims) 0#usize
            let q←Array.index_usize row j
            ok (q,NNG_InstallClaims.lowerClaims claims))=_
 rw [add_shift i bound,bind_tc_ok]
 rw [NNG_LegacyArrays136.index_map (arr toT1) claims 0#usize (by decide),bind_tc_ok]
 have selected := NNG_LegacyArrays136.index_map toT1 (NNG_Array136.get claims 0#usize (by decide)) (shifted i) (by change (shifted i).val<29;exact NNG_Offset16.bound i bound)
 refine (congrArg (fun r : Result AspisR1PublicPreparation.aspis_core.field.QM31=>
   do let q←r;ok (q,NNG_InstallClaims.lowerClaims claims)) selected).trans ?_
 simp only [bind_tc_ok,secondValue,dif_pos bound]
 rfl

theorem array {H : Type} (d : AspisR1PublicPreparation.aspis_core.Digest32 H) (claims : Claims) :
 OraclePortStdBuilder.fromFn 10#usize (AspisR1PublicPreparation.FinishModel.closureFn5 d) (NNG_InstallClaims.lowerClaims claims)=
 .ok (arr toT1 (high claims)) := by
 obtain ⟨value,run,values⟩ := from_fn 10#usize (AspisR1PublicPreparation.FinishModel.closureFn5 d)
   (fun i=>toT1 (secondValue claims i)) (NNG_InstallClaims.lowerClaims claims)
   (by intro i hi;exact callback d claims i (indices_bound 10#usize i hi))
 have same : value=arr toT1 (high claims) := by
   apply Subtype.ext
   rw [values]
   change (OraclePortStdBuilder.indices 10#usize).map (fun i=>toT1 (secondValue claims i))=
     ((OraclePortStdBuilder.indices 10#usize).map (secondValue claims)).map toT1
   rw [List.map_map]
   rfl
 rw [same] at run
 exact run
#print axioms add_shift
#print axioms callback
#print axioms array
end AspisR1.NNG_LegacyHigh136
