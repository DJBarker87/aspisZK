import CuSavingsRetainedFinishRelation
set_option autoImplicit false
namespace AspisR1.CuSavingsRetainedFinishBinding
open Aeneas Aeneas.Std Result AspisR1RhoResumeCaller
open CuSavingsRetainedResumeOrigins CuSavingsLibraConcrete
open CuSavingsRetainedCompositionWeightsInputs CuSavingsRetainedFinishRelation
variable [AspisR1CanonicalReader.Runtime] [AspisR1CanonicalSampler.Shared]
  [AspisR1CanonicalKReader.Runtime] [AspisR1S2Groups.Shared]

def sourceTry {A C : Type} (m : Result (core.result.Result A verifier.Error))
    (f : A → Result (core.result.Result C verifier.Error)) : Result (core.result.Result C verifier.Error) := do
  let r ← m
  match r with
  | .Err error => .ok (.Err error)
  | .Ok value => f value

theorem sourceTry_congr {A C : Type} (m : Result (core.result.Result A verifier.Error))
    (f g : A → Result (core.result.Result C verifier.Error)) (h : ∀x,f x=g x) : sourceTry m f=sourceTry m g := by
  unfold sourceTry
  apply (bind_eq_iff m _ _).mpr
  intro r hr
  cases r with
  | Err error => rfl
  | Ok value => exact h value

def sourceFinish {State : Type} (newer : Bool) (B : Boundaries State)
    (v : AspisR1RhoTransactions.verifier.View) (p : verifier.Prepared) (a : verifier.Accumulator)
    (obs : Option (AspisR1RhoTransactions.verifier.Phase → Result Unit)) :
    Result (core.result.Result Unit verifier.Error) :=
  match p.variant with
  | .S2 => sourceTry (B.claimPrefix v p) fun claim =>
    sourceTry (B.storage p) fun storage => do
      let extra ← extraProjection (arrayMap CuSavingsRetainedResumeWeights.scalar p.semantic_alpha)
      let w : AspisR1S2Groups.Weights := {variant:=.S2,factors:=storage.1,points:=storage.2,extra:=groupExtra extra}
      sourceTry (B.pairGuard w p v.final_message) fun _ =>
        sourceTry (if newer then pairNew B p v.final_message w extra else pairOld B p v.final_message w extra)
          fun pair => B.finalTail v p a obs claim pair
  | _ => B.fallback v p a obs

@[reducible] def binding {State : Type} (newer : Bool) (B : Boundaries State)
    (common : AspisR1RhoTransactions.TxCommon) : AspisR1RhoTransactions.TxCommon :=
  {common with finishRelation:=sourceFinish newer B}

theorem source_equivalence {State : Type} (B : Boundaries State)
    (v : AspisR1RhoTransactions.verifier.View) (p : verifier.Prepared) (a : verifier.Accumulator)
    (obs : Option (AspisR1RhoTransactions.verifier.Phase → Result Unit))
    (ha : ∃ a0 a1,p.alpha=Array.make 2#usize [a0,a1] ∧
      CuSavingsLibraOrigins.Alpha (libra a0) ∧ CuSavingsLibraOrigins.Alpha (libra a1))
    (hc : ∀ (i : Nat) (hi : i<p.semantic_alpha.val.length),CuSavingsRhoInitRow.Canonical (p.semantic_alpha.val[i]'hi)) :
    sourceFinish true B v p a obs=sourceFinish false B v p a obs := by
  unfold sourceFinish
  cases p.variant with
  | S1 => rfl
  | D => rfl
  | S2 =>
    apply sourceTry_congr
    intro claim
    apply sourceTry_congr
    intro storage
    have hs : ∀ i : Fin 10,canonicalK (libraK (semanticAt (arrayMap CuSavingsRetainedResumeWeights.scalar p.semantic_alpha) i)) := by
      intro i
      unfold semanticAt arrayMap
      rw [List.getElem_map]
      exact CuSavingsRetainedResumeWeights.scalar_canonical _ (hc i.val _)
    obtain ⟨extra,he,hcanon⟩ := extra_source_success (arrayMap CuSavingsRetainedResumeWeights.scalar p.semantic_alpha) hs
    simp only [he,bind_tc_ok]
    apply sourceTry_congr
    intro guard
    simp only [Bool.true_eq_false,ite_true,ite_false]
    rw [CuSavingsRetainedFinishRelation.pair_equivalence B p v.final_message _ extra ha hcanon]

#print axioms source_equivalence
#print axioms binding
end AspisR1.CuSavingsRetainedFinishBinding
