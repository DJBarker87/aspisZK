import NIT_FinishArguments
set_option autoImplicit false
namespace AspisR1.NIT_FinishInput
open Aeneas Aeneas.Std Result NIT_Cuts AspisR1Stage2

theorem alphas (proof : Slice U8) (v : verifier.View) (p : verifier.Prepared)
 (a : verifier.Accumulator) (domain : NIG_FinishInput.Domain proof v p a) : alphaCanonical p := by
 intro value member
 obtain ⟨i,bound,index⟩ := List.getElem_of_mem member
 have small : i<2 := by
  rw [p.alpha.property] at bound
  exact bound
 have selected : p.alpha.val[i]?=some value := by rw [List.getElem?_eq_getElem bound,index]
 have word:=domain.alpha i small value selected
 exact NIG_FinishAlpha.canonical value word

theorem primitive (proof : Slice U8) (v : verifier.View) (p : verifier.Prepared)
 (a : verifier.Accumulator) (domain : NIG_FinishInput.Domain proof v p a) :
 p.variant=transport.Variant.S2 ∧ feCanonical p.claim ∧ feCanonical p.kappa ∧
 alphaCanonical p ∧ v.round0.val.length=224 ∧ v.round1.val.length=224 ∧
 v.final_message.val.length=2048 :=
 ⟨domain.s2,NIG_FinishAlpha.canonical _ domain.claim,NIG_FinishAlpha.canonical _ domain.kappa,
 alphas proof v p a domain,domain.round0_words.1,domain.round1_words.1,domain.final_words.1⟩

#print axioms alphas
#print axioms primitive
end AspisR1.NIT_FinishInput
