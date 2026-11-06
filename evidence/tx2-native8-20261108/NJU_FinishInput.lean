import NJU_FinishCore
import NJU_WeakPairDomain
set_option autoImplicit false
namespace AspisR1.NJU_FinishInput
open Aeneas Aeneas.Std Result AspisR1Stage2

/-- Same concrete callers and View slices as NIG_FinishInput.Domain, with all
raw-word clauses dropped. Only final-message length is retained for pair's
initial guard. This is a genuine generalized statement, not a trust row. -/
structure Holds (proof:Slice U8) (v:verifier.View) (p:verifier.Prepared)
 (a:verifier.Accumulator):Prop where
 accumulator:NGM_FinishDomain.AccumulatorDomain a
 s2:p.variant=transport.Variant.S2
 claim:NBO_TailDomain.WideCanonical p.claim
 alpha:∀ i, i<2 → ∀ x,p.alpha.val[i]?=some x→NBO_TailDomain.WideCanonical x
 kappa:NBO_TailDomain.WideCanonical p.kappa
 semantic:∀ q∈p.semantic_alpha.val,NGW_NewInterface.CanonK q
 points:∀ point∈p.z.val,NGW_NewInterface.CanonK point.x ∧ NGW_NewInterface.CanonK point.y
 round0:v.round0.val=(proof.val.drop 7527).take 224
 round1:v.round1.val=(proof.val.drop 7783).take 224
 final:v.final_message.val=(proof.val.drop 8007).take 2048
 final_size:v.final_message.val.length=2048

theorem intrinsic (proof : Slice U8) (v : verifier.View) (p : verifier.Prepared)
 (a : verifier.Accumulator) (h : Holds proof v p a) : NJU_FinishCore.Holds p a :=
 ⟨h.accumulator,h.s2,h.alpha⟩

theorem of_original (proof : Slice U8) (v : verifier.View) (p : verifier.Prepared)
 (a : verifier.Accumulator) (h : NIG_FinishInput.Domain proof v p a) : Holds proof v p a :=
 ⟨h.accumulator,h.s2,h.claim,h.alpha,h.kappa,h.semantic,h.points,h.round0,h.round1,h.final,h.final_words.1⟩

#print axioms intrinsic
#print axioms of_original
end AspisR1.NJU_FinishInput
