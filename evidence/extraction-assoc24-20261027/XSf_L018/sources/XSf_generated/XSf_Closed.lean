import XSf_A2
open Aeneas Aeneas.Std Result
open XRo_Join_Carriers XRo_Join_ResultTransport
set_option autoImplicit false
noncomputable section
namespace XSf_Closed

/-- Only the excluded low sampler uses its CLOSED LPk cohort replacement. -/
def narrowed {H : Type} (D : C.D H) (sem : C.Sem H)
 (proof semantic y1 : Slice U8) (hash : H) (old : Array C.E 29#usize) :
 Result (core.result.Result E.Prepared E.Err × Array C.E 29#usize) := do
 let r ← _root_.verifier.candidate.wide_view proof semantic y1
 match r with
 | .Err e => ok (.Err e,old)
 | .Ok v => XRy_NarrowPrepare.prepare AspisR1Post25Sampler.sampler.low_base_p_digits (ed D) (es sem) v hash old

def installed {H : Type} (D : C.D H) (sem : C.Sem H)
 (proof semantic y1 : Slice U8) (hash : H) (old : Array C.E 29#usize) :
 Result (core.result.Result C.Prepared C.Err × Array C.E 29#usize) := do
 let r ← _root_.verifier.candidate.wide_view proof semantic y1
 match r with
 | .Err e => ok (.Err (ce e),old)
 | .Ok v => AspisR1PublicPreparation.PreparedScratchModel.prepare XRo_Join_Installed.actual D sem (cview v) hash old

theorem prepare {H : Type} (D : C.D H) (sem : C.Sem H)
 (proof semantic y1 : Slice U8) (hash : H) (old : Array C.E 29#usize) :
 mapR (fun (p : core.result.Result E.Prepared E.Err × Array C.E 29#usize) =>
   (inner cprepared ce p.1,p.2)) (narrowed D sem proof semantic y1 hash old) =
 installed D sem proof semantic y1 hash old :=
 XSf_A2.whole AspisR1Post25Sampler.sampler.low_base_p_digits (fun _ => rfl)
   D sem proof semantic y1 hash old

#print axioms prepare
end XSf_Closed
end
