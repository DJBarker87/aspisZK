import NHE_RoundAddresses
import NHE_Polynomial
import RPv_IDa_Deployed
set_option autoImplicit false
noncomputable section
namespace NHE_Round
open Aeneas Aeneas.Std Result AspisR1 LPi_FieldValues
attribute [local instance] Classical.propDecidable
abbrev Error := AspisR1Stage2.verifier.Error

def reply : core.result.Result NE Error → core.result.Result AspisR1Stage2.Stage2Finish.E Error
 | .Ok x => .Ok (FIo_Install.fromE x)
 | .Err e => .Err e

def source (bytes : Slice U8) (alpha claim : NE) : Result (core.result.Result NE Error) := do
 let c0 ← FIo_Native.weights.field bytes 0#usize
 let c4 ← FIo_Native.weights.field bytes 4#usize
 let lhs ← FIo_Native.aspis_core.field.wide_exact.WideExact.add c0 c4
 let rhs ← FIo_Native.aspis_core.field.wide_exact.WideExact.mul_m31 claim 536870912#u32
 if lhs≠rhs then ok (.Err .Relation)
 else
  let out ← NHE_Polynomial.source bytes alpha
  ok (.Ok out)

theorem from_injective : Function.Injective FIo_Install.fromE := by
 intro x y h
 have z := congrArg FIo_Install.toE h
 exact z

theorem cohort (reservation : NP6_StdModel.Reservation) (bytes : Slice U8)
 (alpha claim : NE) (round : Usize) (ha : canonE alpha) (small : round.val<2) :
 FIo_FieldBridge.map reply (source bytes alpha claim)=
 AspisR1Stage2.Stage2Finish.verifier.finishRelationRoundWithOps
  (IDa_Deployed.finish reservation) bytes (FIo_Install.fromE alpha) (FIo_Install.fromE claim) round := by
 obtain ⟨idx,hm,h1,h2⟩ := NHE_RoundAddresses.total round small
 have f0 := NHE_FieldPort.adopted bytes 0#usize (by decide)
 have f4 := NHE_FieldPort.adopted bytes 4#usize (by decide)
 unfold source AspisR1Stage2.Stage2Finish.verifier.finishRelationRoundWithOps
 simp only [IDa_Deployed.finish,←f0,←f4,FIo_FieldBridge.map_bind]
 cases h0 : FIo_Native.weights.field bytes 0#usize with
 | fail e => rfl
 | div => rfl
 | ok c0 =>
  cases h4 : FIo_Native.weights.field bytes 4#usize with
  | fail e => rfl
  | div => rfl
  | ok c4 =>
   have cc0 := NHE_FieldCanonical.success bytes 0#usize (by decide) c0 h0
   have cc4 := NHE_FieldCanonical.success bytes 4#usize (by decide) c4 h4
   obtain ⟨lhs,hl,cl⟩ := NGW_PolynomialAdd.total c0 c4 cc0 cc4
   have add := NGW_CurrentAddPort.adopted c0 c4 cc0 cc4
   rw [hl] at add
   obtain ⟨rhs,hr,_,_⟩ := NGM_RoundScale.total claim
   have scale := NHE_ScalePort.quarter claim
   rw [hr] at scale
   have eq : (FIo_Install.fromE lhs≠FIo_Install.fromE rhs) ↔ lhs≠rhs :=
    not_congr ⟨fun h=>from_injective h,fun h=>congrArg FIo_Install.fromE h⟩
   simp only [FIo_FieldBridge.map,bind_tc_ok,←add,←scale,hl,hr,hm,h1,h2,Port3_FinishStage.ne,eq]
   by_cases bad : lhs≠rhs
   · simp [bad,reply]
   · simp only [bad,if_false,decide_false,Bool.false_eq_true]
     have poly := NHE_Polynomial.cohort bytes alpha ha
     rw [FIn_ExtractInstall.same]
     rw [←poly]
     simp only [FIo_FieldBridge.map_bind]
     cases hp : NHE_Polynomial.source bytes alpha <;> rfl

#print axioms from_injective
#print axioms cohort
end NHE_Round
end
