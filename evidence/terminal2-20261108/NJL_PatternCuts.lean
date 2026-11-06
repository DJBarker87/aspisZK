import NJB_PatternCuts
set_option autoImplicit false
noncomputable section
namespace AspisR1.NJL_PatternCuts
open Aeneas Aeneas.Std Result
open FIv_NativeArithmetic (NQ)
open FIv_NativeValue (Canon decode K)
open NJB_PatternReference (State pattern offset)
/-- NJB_K038/K039: one outer call, exact group/interval/next counter, all
four saved input cells, all26 selectors, SAME immutable borrowed patterns,
and all four returned reply cells. seenTerms denotes that SAME borrowed input,
not a separately written allocation inferred from an integer address. -/
def outer (terms : Fin 14 → NQ) (weights : Fin 26 → NQ) (before : State)
 (g : Fin 4) (reply after seenBefore : State) (seenWeights : Fin 26 → NQ)
 (seenTerms : Fin 14 → NQ) (calls seenGroup start stop next : Nat) : Prop :=
 calls=1 ∧ seenGroup=g.val ∧ start=offset g.castSucc ∧ stop=offset g.succ ∧ next=g.val+1 ∧
 seenBefore=before ∧ seenWeights=weights ∧ seenTerms=terms ∧ ∀ i,after i=reply i
def InnerStep (terms : Fin 14 → NQ) (weights : Fin 26 → NQ) (g : Fin 4) (c : Fin 26) (before after : State) : Prop :=
 ∃ product reply events,
 FIq_Native.field.QM31.mul (terms (pattern c)) (weights c)=ok product ∧
 FIq_Native.field.QM31.add (before g) product=ok reply ∧
 NJB_PatternCuts.inner terms weights before g c product reply events 2 (c.val+1) after
/-- Actual native inner cut and both complete emitted child Results. -/
theorem inner_source (terms : Fin 14 → NQ) (weights : Fin 26 → NQ) (before : State)
 (g : Fin 4) (c : Fin 26) (range : offset g.castSucc≤c.val ∧ c.val<offset g.succ)
 (ht : ∀ i,Canon (terms i)) (hw : ∀ i,Canon (weights i)) (hb : ∀ i,Canon (before i)) :
 ∃ after,NJB_StateUpdates.mulAdd before g (terms (pattern c)) (weights c)=ok after ∧
 InnerStep terms weights g c before after ∧ (∀ i,Canon (after i)) := by
 obtain ⟨product,reply,cp,cr,hp,hr,consume⟩ := NJB_PatternCuts.discharge terms weights before g c ht hw hb
 let after := NJB_StateUpdates.set before g reply
 let events : Fin 2 → NJB_Cuts.Event := ![⟨0,terms (pattern c),weights c⟩,⟨1,before g,product⟩]
 have cut : NJB_PatternCuts.inner terms weights before g c product reply events 2 (c.val+1) after := by
  refine ⟨range.1,range.2,ht _,hw _,hb _,hp,hr,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,?_⟩
  intro i
  simp only [after,NJB_StateUpdates.set,eq_comm]
 refine ⟨after,consume events 2 (c.val+1) after cut,⟨product,reply,events,cp,cr,cut⟩,?_⟩
 intro i
 dsimp only [after,NJB_StateUpdates.set]
 split <;> first | exact hr | exact hb i
/-- The native outer reply is instantiated with the complete actual inner
post-state (all four cells); no partial seed or endpoint premise. -/
theorem outer_source (terms : Fin 14 → NQ) (weights : Fin 26 → NQ) (before : State)
 (g : Fin 4) (ht : ∀ i,Canon (terms i)) (hw : ∀ i,Canon (weights i)) (hb : ∀ i,Canon (before i)) :
 ∃ reply,NJB_PatternReference.inner terms weights g before=ok reply ∧ (∀ i,Canon (reply i)) ∧
 ∀ after seenBefore seenWeights seenTerms calls seenGroup start stop next,
 outer terms weights before g reply after seenBefore seenWeights seenTerms calls seenGroup start stop next →
 NJB_PatternReference.inner terms weights g before=ok after := by
 obtain ⟨reply,call,hr,_⟩ := NJB_PatternReference.inner_result terms weights g before ht hw hb
 refine ⟨reply,call,hr,?_⟩
 intro after seenBefore seenWeights seenTerms calls seenGroup start stop next cut
 have frame := cut.2.2.2.2.2.2.2.2
 have same : after=reply := funext frame
 rw [same]
 exact call
#print axioms inner_source
#print axioms outer_source
end AspisR1.NJL_PatternCuts
end
