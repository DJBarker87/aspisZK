import NLB_Windows
set_option autoImplicit false
noncomputable section
namespace NLB_C01Domain
open Aeneas Aeneas.Std Result VTop_Stages AspisR1 NJU_CommonObserved

def Holds (ck proof pub : Slice U8) : Event → Prop
 | .resume c pr pu _ => c=ck ∧ pr=proof ∧ pu=pub
 | _ => True

theorem source (wr rr : NP6_StdModel.Reservation) (merkle : Merkle) (finish : Finish)
 {H : Type} (d : aspis_core.digest.Digest32 H) (pub proof ck : Slice U8) (hash : H) :
 NKE_EventAll.Holds (Holds ck proof pub)
  (run wr rr merkle finish d pub proof ck hash none) := by
 unfold run
 repeat' first
 | nke_zeta
 | nke_bind
 | nke_intro
 | nke_lift
 | nke_pure
 | (apply NKE_EventAll.record_all; first | exact ⟨rfl,rfl,rfl⟩ | exact True.intro)
 | (fail_if_no_progress dsimp only [NJU_Log.prod_cases])
 | split
#print axioms source
end NLB_C01Domain
