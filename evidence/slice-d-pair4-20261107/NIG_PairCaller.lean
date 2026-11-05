import NIG_PairCanonical
import NIG_PairInputs
set_option autoImplicit false
noncomputable section
namespace NIG_PairCaller
open Aeneas Aeneas.Std Result AspisR1 AspisR1Stage2 LPi_FieldValues
abbrev E:=aspis_core.field.wide_exact.WideExact

theorem source (r:NP6_StdModel.Reservation) (proof:Slice U8)
 (v:verifier.View) (p:verifier.Prepared) (a:verifier.Accumulator)
 (domain:NIG_FinishInput.Domain proof v p a) (w:FIo_Install.W)
 (new:(NIG_Slots.installed r).op3 p.variant p.semantic_alpha p.z=ok (.Ok w))
 (out:E) (run:FIo_Install.pair r w p.alpha.to_slice v.final_message p.kappa=ok (.Ok out)):
 canonE (FIo_Install.toE out):=by
 obtain ⟨s2,hf,he⟩:=NIG_PairInputs.new_owner r proof v p a domain w new
 unfold FIo_Install.pair at run
 obtain ⟨reply,hr,run⟩:=Port3_PushFrame.bind_success _ _ _ run
 cases reply with
 | Err e=>cases run
 | Ok value=>
  cases core.result.Result.Ok.inj (Result.ok.inj run)
  exact NIG_PairCanonical.source r (FIo_Install.toWeights w) p v.final_message
   (FIo_Install.toE p.kappa) value (NIG_PairInputs.final_width proof v p a domain)
   s2 hf he (NIG_FinishAlpha.canonical p.kappa domain.kappa)
   (NIG_PairInputs.alphas proof v p a domain) hr
#print axioms source
end NIG_PairCaller
