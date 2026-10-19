import AspisV8R19.SourceDuplexStep

/-! A one-step counting bound for an independently uniform 32-byte state.
Not a bound for adversarially chosen states, whole runs or publication. -/
set_option autoImplicit false
namespace AspisV8R19.UniformStateFirstHit
open DuplexFrames SourceDuplexStep
noncomputable section

def badStates {S : Type*} [Fintype S] (encode : S → Bytes) (reads : List Bytes) : Finset S := by
  classical
  exact Finset.univ.filter (fun s => BadState reads (encode s))

theorem bytes_injective : Function.Injective bytes := by
  intro s t h
  exact List.ofFn_injective h

theorem bad_states_card {S : Type*} [Fintype S] (encode : S → Bytes)
    (hlen : ∀ s, (encode s).length = 32) (hinj : Function.Injective encode)
    (reads : List Bytes) : (badStates encode reads).card ≤ reads.length := by
  classical
  apply le_trans (b := (blocked reads).card)
  · apply Finset.card_le_card_of_injOn encode
    · intro s hs
      have hm : BadState reads (encode s) := by
        simpa only [Finset.mem_coe, badStates, Finset.mem_filter, Finset.mem_univ, true_and] using hs
      exact bad_mem_blocked reads (encode s) (hlen s) hm
    · intro s _ t _ h
      exact hinj h
  · exact blocked_card reads

theorem state_card : Fintype.card State = 256 ^ 32 := by
  simp [State, Byte, Fintype.card_fun]

def uniformBadFraction (reads : List Bytes) : ℚ :=
  (badStates bytes reads).card / (Fintype.card State : ℚ)

theorem uniform_bad_bound (reads : List Bytes) :
    uniformBadFraction reads ≤ (reads.length : ℚ) / (256 ^ 32 : ℚ) := by
  unfold uniformBadFraction
  rw [state_card]
  simp only [Nat.cast_pow, Nat.cast_ofNat]
  exact div_le_div_of_nonneg_right
    (by exact_mod_cast bad_states_card bytes bytes_length bytes_injective reads) (by positivity)

#print axioms bytes_injective
#print axioms bad_states_card
#print axioms state_card
#print axioms uniform_bad_bound
end
end AspisV8R19.UniformStateFirstHit
