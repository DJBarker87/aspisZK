import ARR_FreshState
set_option autoImplicit false
noncomputable section
namespace AspisR1.ARR_FactoryLoss
open Aeneas Aeneas.Std Result
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw

theorem state_card : Fintype.card State = 256^32 := by
  change Fintype.card (Fin 32 → Fin 256) = _
  simp only [Fintype.card_fun,Fintype.card_fin]

/-- Every property of the ORIGINAL complete run is retained in the excluded
world. `good` may include selected entries, bank-game observations, successful
or rejected outcome and arbitrary original cost predicates. This generic theorem
does not assert an instance of all retained Rc10 hypotheses. -/
theorem same_execution {X : Type} (p : Program Bytes State X) (H : Bytes → State)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (good : List (Bytes × State) × X → Prop) (original : good (eval H p))
    (bound : (eval H p).1.length < 256^32)
    (return32 : ∀ s : State, ∃ digest, hashv (ARR_FreshState.parts s) = .ok digest) :
    ∃ K : Bytes → State,
      eval K p = eval H p ∧ good (eval K p) ∧
      ¬ ∃ sha256 : Bytes → State, S2W_ExtractionBoundary.P1 sha256 K ∧
        S2W_ExtractionBoundary.RuntimeSyscall hashv sha256 := by
  obtain ⟨s,fresh⟩ := ARR_FreshState.fresh ((eval H p).1.map Prod.fst)
    (by rw [List.length_map,state_card]; exact bound)
  obtain ⟨digest,returned⟩ := return32 s
  obtain ⟨K,same,bad⟩ := ARR_OffPath.incompatible_same_run p H hashv
    (ARR_FreshState.parts s) digest returned (by rw [ARR_FreshState.flatten_parts]; exact fresh)
  refine ⟨K,same,?_,?_⟩
  · rw [same]
    exact original
  · exact fun witness => bad ((ARR_WorldCompatibility.iff_witness K hashv).mpr witness)

/-- Uniform query budgets do not rescue the global factory. The condition
on return32 is explicit and is NOT adopted as a new runtime trust item. -/
theorem bounded_no_factory {X : Type} (p : Program Bytes State X)
    (accepts : X → Prop) (H : Bytes → State)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (accepted : accepts (eval H p).2) (N : Nat)
    (queries : ∀ K, (eval K p).1.length ≤ N) (small : N < 256^32)
    (return32 : ∀ s : State, ∃ digest, hashv (ARR_FreshState.parts s) = .ok digest) :
    ¬ ∀ K : Bytes → State, accepts (eval K p).2 →
      ∃ sha256 : Bytes → State, S2W_ExtractionBoundary.P1 sha256 K ∧
        S2W_ExtractionBoundary.RuntimeSyscall hashv sha256 := by
  apply ARR_FreshState.no_factory p accepts H hashv accepted
  · rw [state_card]
    exact (queries H).trans_lt small
  · exact return32

#print axioms state_card
#print axioms same_execution
#print axioms bounded_no_factory
end AspisR1.ARR_FactoryLoss
end
