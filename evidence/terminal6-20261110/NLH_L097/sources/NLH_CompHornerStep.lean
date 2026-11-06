import NKI_InitialPrefix
import NLH_CompositionState
import NLH_TermHornerCut
set_option autoImplicit false
noncomputable section
namespace AspisR1.NLH_CompHornerStep
open Aeneas Aeneas.Std Result FIq_Native NLH_CompositionState
open FIv_NativeArithmetic (NQ)
open FIv_NativeValue (Canon)
open NKI_InitialPrefix (Public)
theorem source (pub : Public) (claims : Array NQ 84#usize) (point : Array NQ 10#usize)
 (lambda chi theta : NQ) (st : State) (i : Fin 28) (lane : NQ) (rest : List NQ)
 (remaining : st.remaining=lane::rest) (ht : Canon theta) (hc : Canon st.composition)
 (hl : Canon lane) (hp : NJB_PreparedLaws.Domain st.prepared theta) :
 ∃ product out,field.PreparedQm31Multiplier.mul st.prepared st.composition=ok product ∧
 field.QM31.add product lane=ok out ∧
 step pub claims point lambda chi theta (.horner i) st=ok (.Ok {st with composition := out,remaining := rest}) ∧
 Canon out ∧ NLH_TermHornerCut.Cut st.prepared st.composition lane product out
   (NLH_TermHornerCut.observation st.prepared st.composition lane product out) := by
 obtain ⟨product,out,pm,ma,_,co,cut⟩ := NLH_TermHornerCut.step_source st.prepared theta st.composition lane ht hc hl hp
 exact ⟨product,out,pm,ma,by simp only [step,remaining,pm,ma,bind_tc_ok],co,cut⟩
#print axioms source
end AspisR1.NLH_CompHornerStep
end
