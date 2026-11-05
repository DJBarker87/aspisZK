import NHE_PrivateDot
import NFG_PublicG
set_option autoImplicit false
namespace NHE_CheckedScalar
open Aeneas Aeneas.Std Result AspisR1
abbrev NQ := FIo_Native.aspis_core.field.QM31
abbrev PushQm := AspisR1EbyKPushDotBackend.PushQm

def toPush (q : NQ) : PushQm := ⟨⟨q.c0.a,q.c0.b⟩,⟨q.c1.a,q.c1.b⟩⟩

theorem checked (q : NQ) :
 AspisR1EbyKCheckedQAllParamV1.checkedQWithAll AspisR1EbyKCheckedQConcreteAll.concreteAll (toPush q)=
 FIo_Native.fast_pairing.checked_q q := by
 rw [NFG_PublicG.check_result]
 simp only [AspisR1EbyKCheckedQAllParamV1.checkedQWithAll,AspisR1EbyKCheckedQAllParamV1.limbsOf,AspisR1EbyKCheckedQAllParamV1.fromLimbsWithAll,AspisR1EbyKCheckedQConcreteAll.concreteAll,AspisR1EbyKCheckedQConcreteAll.allRun,AspisR1EbyKCheckedQAllParamV1.fromLimbsClosureFnMut,AspisR1EbyKCheckedQAllParamV1.fromLimbsClosureCallMut,AspisR1EbyKCheckedQAllParamV1.P,toPush,Array.to_slice,core.slice.Slice.iter,Array.make,List.drop_zero,lift,bind_tc_ok]
 split_ifs <;> simp_all [NFG_PublicG.Valid,AspisR1EbyKCheckedQAllParamV1.optionOkOr,NFE_NFC_CalleeDomains.q]

 all_goals first | rfl | (split_ifs <;> simp_all [bind_tc_ok])

#print axioms checked
end NHE_CheckedScalar
