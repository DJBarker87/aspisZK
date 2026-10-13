import R0P.Poseidon

/-! A generic finite-state combiner from the explicit 4+14+4 Poseidon round
transitions to the already-defined permutation. The round functions stay
opaque: the proof folds the supplied symbolic transitions only. -/
set_option autoImplicit false
namespace R0P

private theorem foldl_compose_steps {σ : Type} {n : Nat}
    (states : Fin (n + 1) → σ) (steps : Fin n → σ → σ)
    (h : ∀ i : Fin n, states i.succ = steps i (states i.castSucc)) :
    (List.ofFn steps).foldl (fun state step => step state) (states 0) =
      states (Fin.last n) := by
  induction n with
  | zero => simp only [List.ofFn_zero, List.foldl_nil, Fin.last_zero]
  | succ n ih =>
    rw [List.ofFn_succ, List.foldl_cons]
    have hz := h 0
    change states (Fin.succ 0) = steps 0 (states 0) at hz
    rw [← hz]
    exact ih (fun i => states i.succ) (fun i => steps i.succ)
      (fun i => h i.succ)

private theorem foldl_rounds_eq_last {σ α : Type} {n : Nat}
    (states : Fin (n + 1) → σ) (parameters : Fin n → α)
    (round : σ → α → σ)
    (h : ∀ i : Fin n, states i.succ =
      round (states i.castSucc) (parameters i)) :
    (List.ofFn parameters).foldl (fun state parameter => round state parameter)
      (states 0) = states (Fin.last n) := by
  have hfold : (List.ofFn parameters).foldl
      (fun state parameter => round state parameter) (states 0) =
      (List.ofFn (fun i : Fin n => i)).foldl
        (fun state i => round state (parameters i)) (states 0) := by
    calc
      _ = ((List.ofFn (fun i : Fin n => i)).map parameters).foldl
          (fun state parameter => round state parameter) (states 0) := by
            rw [List.map_ofFn]
            rfl
      _ = _ := List.foldl_map
  rw [hfold]
  exact foldl_compose_steps states
    (fun i state => round state (parameters i)) h

theorem poseidon_chain {K : Type} [Field K]
    (y : Fin 24 → (Fin 16 → K))
    (hlead : y 1 = poseidonExternalLinear (y 0))
    (hinitial : ∀ r : Fin 4,
      y ⟨2 + r.val, by omega⟩ =
        poseidonFullRound (y ⟨1 + r.val, by omega⟩)
          (poseidonExternalInitial (K := K) r))
    (hinternal : ∀ r : Fin 14,
      y ⟨6 + r.val, by omega⟩ =
        poseidonInternalRound (y ⟨5 + r.val, by omega⟩)
          (poseidonInternalConstants (K := K) r))
    (hfinal : ∀ r : Fin 4,
      y ⟨20 + r.val, by omega⟩ =
        poseidonFullRound (y ⟨19 + r.val, by omega⟩)
          (poseidonExternalFinal (K := K) r)) :
    poseidonPermutation (y 0) = y 23 := by
  let initialStates : Fin 5 → (Fin 16 → K) :=
    fun i => y ⟨1 + i.val, by omega⟩
  let internalStates : Fin 15 → (Fin 16 → K) :=
    fun i => y ⟨5 + i.val, by omega⟩
  let finalStates : Fin 5 → (Fin 16 → K) :=
    fun i => y ⟨19 + i.val, by omega⟩
  have hInitial : ∀ r : Fin 4, initialStates r.succ =
      poseidonFullRound (initialStates r.castSucc)
        (poseidonExternalInitial (K := K) r) := by
    intro r
    simpa [initialStates, Fin.val_succ] using hinitial r
  have hInternal : ∀ r : Fin 14, internalStates r.succ =
      poseidonInternalRound (internalStates r.castSucc)
        (poseidonInternalConstants (K := K) r) := by
    intro r
    simpa [internalStates, Fin.val_succ] using hinternal r
  have hFinal : ∀ r : Fin 4, finalStates r.succ =
      poseidonFullRound (finalStates r.castSucc)
        (poseidonExternalFinal (K := K) r) := by
    intro r
    simpa [finalStates, Fin.val_succ] using hfinal r
  unfold poseidonPermutation
  rw [hlead]
  rw [foldl_rounds_eq_last initialStates
    (poseidonExternalInitial (K := K)) poseidonFullRound hInitial]
  rw [foldl_rounds_eq_last internalStates
    (poseidonInternalConstants (K := K)) poseidonInternalRound hInternal]
  rw [foldl_rounds_eq_last finalStates
    (poseidonExternalFinal (K := K)) poseidonFullRound hFinal]
  rfl

#print axioms poseidon_chain

end R0P
