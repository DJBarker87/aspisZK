import NIW_AlignFinishComposed
set_option autoImplicit false
noncomputable section
namespace AspisR1.NIW_AlignFinishPairCertificate
open Aeneas Aeneas.Std Result NIT_Cuts AspisR1Stage2 NIW_AlignFinishComposed

def Linked (r : NP6_StdModel.Reservation) (info : PairInfo) : Prop :=
 let loc := info.locations
 let i := NIW_AlignPairInstalled.input info.owner info.alpha info.message info.kappa
  loc.ap0 loc.ap1 loc.common loc.low loc.scratch loc.parts
 info.native=NIW_AlignPairPhase.run r i ∧
 NIT_PairDomain.Domain (FIo_Install.toWeights info.owner.value)
  (NFW_PowersCohort.mapArray FIo_Install.toE info.alpha.value) info.message.value (FIo_Install.toE info.kappa) ∧
 NIW_AlignPairPhase.Certificate r i info.native ∧
 FIo_Install.pair r info.owner.value info.alpha.value.to_slice info.message.value info.kappa=
  NIT_ErrorTransport.full info.native.1 ∧ NIT_ResultCanonical.Canonical info.native.1

def Bound (r : NP6_StdModel.Reservation) : Option PairInfo → Prop
 | none => True
 | some info => Linked r info

theorem observe_bound {A B : Type} (r : NP6_StdModel.Reservation) (call : Result (Reply A))
 (event : Result (Reply A) → Event) (next : A → Observed B)
 (tail : ∀ value,call=ok (.Ok value) → Bound r (next value).2.2) :
 Bound r (observe call event next).2.2 := by
 cases call with
 | fail err => trivial
 | div => trivial
 | ok reply =>
  cases reply with
  | Err err => trivial
  | Ok value => exact tail value rfl

/-- The nested pair certificate uses the actual complete Result in the SAME
finish invocation. Its domain is proved from the actual NEW return generated
by the source interpreter. No successful-NEW or pair endpoint premise remains. -/
theorem source (r : NP6_StdModel.Reservation) (loc : Locations) (proof : Slice U8)
 (v : verifier.View) (p : verifier.Prepared) (a : verifier.Accumulator)
 (domain : NIG_FinishInput.Domain proof v p a) : Bound r (run r loc v p a).2.2 := by
 unfold run
 apply observe_bound
 intro first firstCall
 apply observe_bound
 intro claim claimCall
 apply observe_bound
 intro owner newCall
 have caller := NIT_PairDomain.caller r proof v p a domain owner newCall
 have pair := NIW_AlignPairInstalled.source r ⟨loc.owner,owner⟩ ⟨loc.alpha,p.alpha⟩
  ⟨loc.message,v.final_message⟩ p.kappa loc.ap0 loc.ap1 loc.common loc.low loc.scratch loc.parts caller
 exact ⟨rfl,caller,NIW_AlignPairPhase.certificate r _ caller,pair⟩

#print axioms observe_bound
#print axioms source
end AspisR1.NIW_AlignFinishPairCertificate
