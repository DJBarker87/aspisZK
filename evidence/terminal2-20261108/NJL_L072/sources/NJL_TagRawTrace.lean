import NJL_TagRawStep
set_option autoImplicit false
noncomputable section
namespace AspisR1.NJL_TagRawTrace
open Aeneas Aeneas.Std Result
open NJB_TagRaw (B)
open NJL_TagRawStep (State Event)
abbrev Selectors := FIq_Native.pool_v1.pair_forest_copy_terminal.Selectors
def dot (s : Selectors) (xs : List (Fin 272)) (limb : Fin 4) : Nat :=
 (xs.map (fun t=>(NJL_TagWords.highWord s t limb).val*(NJL_TagWords.tagWord t).val)).sum
def run (s : Selectors) : List (Fin 272) → State → Result State
 | [],before=>ok before
 | t::ts,before=>do
  let after ← NJL_TagRawStep.reference s t before
  run s ts after
inductive Trace (s : Selectors) : List (Fin 272) → Nat → State → State → Prop
 | nil (k : Nat) (before : State) : Trace s [] k before before
 | cons {t ts k before middle after}
   (step : ∃ products events,NJL_TagRawStep.reference s t before=ok middle ∧
    NJL_TagRawStep.Cut s t before middle products events 4 (t.val+1) ∧
    ∀ i,UScalar.mul (NJL_TagWords.highWord s t i) (NJL_TagWords.tagWord t)=ok (products i) ∧
     (products i).val=(NJL_TagWords.highWord s t i).val*(NJL_TagWords.tagWord t).val ∧ (products i).val≤B)
   (rest : Trace s ts (k+1) middle after) : Trace s (t::ts) k before after
/-- Finite induction over at most four terms; every step supplies the actual
checked integer products and additions on the SAME limb carriers. -/
theorem source (s : Selectors) (xs : List (Fin 272)) (before : State) (k : Nat)
 (small : k+xs.length≤4) (hs : FIw_ArrayValue.canonical s.high)
 (hb : ∀ i,(before i).val≤k*B) :
 ∃ after,run s xs before=ok after ∧ Trace s xs k before after ∧
 (∀ i,(after i).val=(before i).val+dot s xs i) ∧
 (∀ i,(after i).val≤(k+xs.length)*B) := by
 induction xs generalizing k before with
 | nil =>
  refine ⟨before,rfl,.nil k before,?_,?_⟩
  · intro i;simp [dot]
  · simpa using hb
 | cons t ts ih =>
  have hk : k<4 := by simp only [List.length_cons] at small;omega
  obtain ⟨products,middle,events,call,cut,productsLaw,_,hm⟩ := NJL_TagRawStep.source s t before k hk hs hb
  obtain ⟨after,rest,tr,values,bounds⟩ := ih middle (k+1) (by simp only [List.length_cons] at small;omega) hm
  refine ⟨after,?_,.cons ⟨products,events,call,cut,productsLaw⟩ tr,?_,?_⟩
  · simp only [run,call,bind_tc_ok,rest]
  · intro i
    rw [values i,cut.2.2.2 i,(productsLaw i).2.1]
    simp only [dot,List.map_cons,List.sum_cons]
    omega
  · intro i
    have h := bounds i
    simpa only [List.length_cons,Nat.add_assoc,Nat.add_comm 1] using h
#print source
#print axioms source
end AspisR1.NJL_TagRawTrace
end
