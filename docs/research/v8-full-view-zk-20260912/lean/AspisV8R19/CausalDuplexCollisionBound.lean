import AspisV8R19.CausalInjectiveFrameBound
import AspisV8R19.UniformStateFirstHit

/-! Causal collision loss for byte-prefixed duplex addresses.

Every selected duplex address begins with the current 32-byte state.  Thus a
collision with any prior address implies that the current state bytes occur in
the list of prior 32-byte prefixes.  This file combines that deterministic
fact with the causal injective-frame theorem.  It still leaves the actual
callback-to-tape instantiation and its operation-count bounds explicit. -/
set_option autoImplicit false
namespace AspisV8R19.CausalDuplexCollisionBound

open DuplexFrames SourceDuplexStep
open OracleResampling CausalFirstHitUnionBound CausalTapeFirstHit
open CausalInjectiveFrameBound UniformStateFirstHit

def priorPrefixes (reads : List Bytes) : List Bytes :=
  reads.map (fun address => address.take 32)

def blockedAt {n : Nat}
    (priorReads : (i : Fin n) → (Fin i.val → State) → List Bytes)
    (i : Fin n) (history : Fin i.val → State) (s : State) : Prop :=
  bytes s ∈ priorPrefixes (priorReads i history)

theorem frame_collision_implies_blocked
    (prior current : List Bytes) (s : State)
    (prefixed : ∀ address ∈ current, address.take 32 = bytes s)
    (collision : ∃ address ∈ current, address ∈ prior) :
    bytes s ∈ priorPrefixes prior := by
  obtain ⟨address, hcurrent, hprior⟩ := collision
  unfold priorPrefixes
  exact List.mem_map.mpr ⟨address, hprior, prefixed address hcurrent⟩

theorem causal_duplex_blocked_bound {n : Nat}
    (priorReads : (i : Fin n) → (Fin i.val → State) → List Bytes)
    (limit : Fin n → Nat)
    (hlen : ∀ i history, (priorReads i history).length ≤ limit i) :
    mean (fun tape : Fin n → State => indicator (∃ i,
      event (blockedAt priorReads) i tape)) ≤
      ∑ i, (limit i : ℚ) / (256 ^ 32 : ℚ) := by
  have h := causal_injective_frame_firstHit_le
    (S := State) (I := Bytes)
    (fun _i _history => bytes)
    (fun i history => priorPrefixes (priorReads i history))
    limit
    (fun _i _history => bytes_injective)
    (fun i history => by
      simpa only [priorPrefixes, List.length_map] using hlen i history)
  rw [state_card] at h
  have hbad :
      frameBad (fun _i _history => bytes)
        (fun i history => priorPrefixes (priorReads i history)) =
      blockedAt priorReads := by
    funext i history s
    rfl
  rw [hbad] at h
  simpa only [Nat.cast_pow, Nat.cast_ofNat] using h

theorem sum_two_prior_slots (n : Nat) :
    (∑ i : Fin n, (2 * i.val : ℚ)) = (n : ℚ) * (n - 1 : Nat) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Fin.sum_univ_succ]
      simp only [Fin.val_zero, Nat.cast_zero, mul_zero, zero_add, Fin.val_succ,
        Nat.cast_add, Nat.cast_one, Nat.succ_sub_one]
      calc
        (∑ i : Fin n, (2 : ℚ) * (i.val + 1)) =
            ∑ i : Fin n, ((2 : ℚ) * i.val + 2) := by
          apply Finset.sum_congr rfl
          intro i _
          ring
        _ = (∑ i : Fin n, (2 : ℚ) * i.val) + ∑ _i : Fin n, (2 : ℚ) := by
          rw [Finset.sum_add_distrib]
        _ = (n : ℚ) * (n - 1 : Nat) + 2 * n := by
          rw [ih]
          simp
          ring
        _ = ((n : ℚ) + 1) * n := by
          by_cases hn : n = 0
          · subst n
            norm_num
          · have hsub : ((n - 1 : Nat) : ℚ) = (n : ℚ) - 1 := by
              rw [Nat.cast_sub (by omega)]
              norm_num
            rw [hsub]
            ring

theorem sum_cast_two_prior_slots (n : Nat) :
    (∑ i : Fin n, ((2 * i.val : Nat) : ℚ)) =
      (n : ℚ) * (n - 1 : Nat) := by
  simpa only [Nat.cast_mul, Nat.cast_ofNat] using sum_two_prior_slots n

theorem causal_duplex_two_address_bound {n : Nat}
    (priorReads : (i : Fin n) → (Fin i.val → State) → List Bytes)
    (hlen : ∀ i history, (priorReads i history).length ≤ 2 * i.val) :
    mean (fun tape : Fin n → State => indicator (∃ i,
      event (blockedAt priorReads) i tape)) ≤
      ((n : ℚ) * (n - 1 : Nat)) / (256 ^ 32 : ℚ) := by
  have h := causal_duplex_blocked_bound priorReads (fun i => 2 * i.val) hlen
  rw [← Finset.sum_div, sum_cast_two_prior_slots] at h
  exact h

#print axioms frame_collision_implies_blocked
#print axioms causal_duplex_blocked_bound
#print axioms sum_two_prior_slots
#print axioms sum_cast_two_prior_slots
#print axioms causal_duplex_two_address_bound

end AspisV8R19.CausalDuplexCollisionBound
