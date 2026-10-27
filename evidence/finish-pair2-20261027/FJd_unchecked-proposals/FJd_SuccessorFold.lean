import FJd_SourceSuccessor
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJd_SuccessorFold
open Aeneas Aeneas.Std Result
open FJc_WeightQMBridge (SQ)
open FJc_WeightValues
abbrev State := SQ × (Fin 10 → SQ)
def reference (z : Fin 10 → SQ) : List (Fin 10) → State → Result State
  | [],state => ok state
  | i::xs,state => do
    let (carry,out) ← FJd_SourceSuccessor.reference (z i) state.1
    reference z xs (carry,Function.update state.2 i out)
def CanonState (s : State) : Prop := Canon s.1 ∧ ∀ i,Canon (s.2 i)
def decoded (s : State) := (decode s.1,fun i=>decode (s.2 i))

theorem update_decode (out : Fin 10 → SQ) (i : Fin 10) (x : SQ) :
    (fun j=>decode (Function.update out i x j))=
      Function.update (fun j=>decode (out j)) i (decode x) := by
  funext j
  by_cases h : j=i
  · subst j;simp only [Function.update_self]
  · simp only [Function.update_of_ne h]

theorem value (xs : List (Fin 10)) (z : Fin 10 → SQ) (before after : State)
    (hz : ∀ i,Canon (z i)) (hb : CanonState before)
    (run : reference z xs before=ok after) :
    CanonState after ∧ decoded after=
      xs.foldl (FJd_LoopReference.successorStep (fun i=>decode (z i))) (decoded before) := by
  induction xs generalizing before with
  | nil =>
    cases Result.ok.inj run
    exact ⟨hb,rfl⟩
  | cons i xs ih =>
    simp only [reference] at run
    obtain ⟨step,hs,run⟩ := Port3_PushFrame.bind_success _ _ _ run
    rcases step with ⟨carry,out⟩
    have hv := FJd_SourceSuccessor.value (z i) before.1 carry out (hz i) hb.1 hs
    have hc : CanonState (carry,Function.update before.2 i out) := by
      refine ⟨hv.1,?_⟩
      intro j
      by_cases h : j=i
      · subst j;simpa only [Function.update_self] using hv.2.1
      · simpa only [Function.update_of_ne h] using hb.2 j
    obtain ⟨canon,hvalue⟩ := ih _ hc run
    refine ⟨canon,?_⟩
    rw [List.foldl_cons,hvalue]
    congr 1
    apply Prod.ext
    · exact hv.2.2.1
    · dsimp [decoded,FJd_LoopReference.successorStep]
      rw [update_decode,hv.2.2.2]
      congr 1
      ring
#print axioms update_decode
#print axioms value
end AspisR1.FJd_SuccessorFold
end
