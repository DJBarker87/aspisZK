import AspisV8R19.DuplexFrames
import AspisV8R19.DuplexFreshPair

/-! Exact byte-address step and a conservative finite first-hit support.
The oracle returns 32-byte states. No SHA randomness or source-causal-policy
refinement is assumed. The finite pair law lives in DuplexFreshPair; this
byte-address bridge is an explicit trace-preserving bijection. -/
set_option autoImplicit false
namespace AspisV8R19.SourceDuplexStep
open DuplexFrames DuplexFreshPair AspisV8R17.AdaptiveOracle
abbrev State := Fin 32 → Byte
def bytes (s : State) : Bytes := List.ofFn s
def step (H : Bytes → State) (s : State) : State × State :=
  (H (squeeze (bytes s)), H (advance (bytes s)))
def calls (H : Bytes → State) (s : State) : List (Bytes × State) :=
  [(squeeze (bytes s), (step H s).1), (advance (bytes s), (step H s).2)]
def blocked (reads : List Bytes) : Finset Bytes :=
  (reads.map (fun p => p.take 32)).toFinset

theorem bytes_length (s : State) : (bytes s).length = 32 := by simp [bytes]

theorem advance_uses_prestate (H : Bytes → State) (s : State) :
    (calls H s)[1]? = some (advance (bytes s), H (advance (bytes s))) := rfl

theorem unread_squeeze (tr : List (Bytes × State)) (s : State)
    (fresh : Fresh (tr.map Prod.fst) (bytes s)) :
    ∀ p ∈ tr, p.1 ≠ squeeze (bytes s) := by
  intro p hp h
  apply fresh.1
  exact List.mem_map.mpr ⟨p, hp, h⟩

theorem unread_advance (tr : List (Bytes × State)) (s : State)
    (fresh : Fresh (tr.map Prod.fst) (bytes s)) :
    ∀ p ∈ tr, p.1 ≠ advance (bytes s) := by
  intro p hp h
  apply fresh.2
  exact List.mem_map.mpr ⟨p, hp, h⟩

def sourceFiberEquiv (next : List (Bytes × State) → Bytes) (n : ℕ)
    (tr : List (Bytes × State)) (s : State)
    (fresh : Fresh (tr.map Prod.fst) (bytes s)) (e f : State ≃ State) (a b : State) :
    {H : Bytes → State // run next H n [] = tr ∧ (step H s).1 = a ∧ (step H s).2 = b} ≃
    {H : Bytes → State // run next H n [] = tr ∧ (step H s).1 = e a ∧ (step H s).2 = f b} :=
  tracePairFiberEquiv next n tr (squeeze (bytes s)) (advance (bytes s))
    (cross_disjoint _ _) (unread_squeeze tr s fresh) (unread_advance tr s fresh) e f a b

theorem step_under_reindex (H : Bytes → State) (s : State) (e f : State ≃ State) :
    step (pairEquiv (squeeze (bytes s)) (advance (bytes s)) e f H) s =
      (e (step H s).1, f (step H s).2) := by
  apply Prod.ext
  · exact pair_at_first _ _ (cross_disjoint _ _) e f H
  · exact pair_at_second _ _ (cross_disjoint _ _) e f H

theorem next_pair_fresh (tr : List (Bytes × State)) (H : Bytes → State) (s : State) :
    Fresh ((tr ++ calls H s).map Prod.fst) (bytes (step H s).2) ↔
      Fresh (tr.map Prod.fst) (bytes (step H s).2) ∧ bytes (step H s).2 ≠ bytes s := by
  simp only [List.map_append, calls, List.map_cons, List.map_nil]
  exact fresh_after_pair _ _ _

theorem bad_mem_blocked (reads : List Bytes) (s : Bytes) (hs : s.length = 32)
    (bad : BadState reads s) : s ∈ blocked reads := by
  rcases bad with ⟨p, hp, h | h⟩ <;> subst p
  · have take : (squeeze s).take 32 = s := by
      simp [squeeze, List.take_append, hs, List.take_of_length_le (by omega : s.length ≤ 32)]
    exact List.mem_toFinset.mpr (List.mem_map.mpr ⟨squeeze s, hp, take⟩)
  · have take : (advance s).take 32 = s := by
      simp [advance, List.take_append, hs, List.take_of_length_le (by omega : s.length ≤ 32)]
    exact List.mem_toFinset.mpr (List.mem_map.mpr ⟨advance s, hp, take⟩)

theorem blocked_card (reads : List Bytes) : (blocked reads).card ≤ reads.length := by
  exact (List.toFinset_card_le _).trans (by simp)

theorem repeated_state_repeats (H : Bytes → State) (s : State)
    (fixed : (step H s).2 = s) :
    step H (step H s).2 = step H s ∧
      ¬ Fresh ((calls H s).map Prod.fst) (bytes (step H s).2) := by
  rw [fixed]
  constructor
  · rfl
  · exact repeated_state_not_fresh [] (bytes s)

#print axioms bytes_length
#print axioms advance_uses_prestate
#print axioms unread_squeeze
#print axioms unread_advance
#print axioms sourceFiberEquiv
#print axioms step_under_reindex
#print axioms next_pair_fresh
#print axioms bad_mem_blocked
#print axioms blocked_card
#print axioms repeated_state_repeats
end AspisV8R19.SourceDuplexStep
