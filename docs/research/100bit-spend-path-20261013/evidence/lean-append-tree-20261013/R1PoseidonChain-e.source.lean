import R0P.Poseidon

/-! A generic finite-state combiner from the explicit 4+14+4 Poseidon round
transitions to the already-defined permutation. The round functions stay
opaque: the proof folds the supplied symbolic transitions only. -/
set_option autoImplicit false
namespace R0P

private theorem foldl_compose_steps {σ α : Type} {n : Nat}
    (states : Fin (n + 1) → σ) (parameters : Fin n → α)
    (round : σ → α → σ)
    (h : ∀ i : Fin n, states i.succ =
      round (states i.castSucc) (parameters i)) :
    (List.ofFn parameters).foldl (fun state parameter => round state parameter)
      (states 0) = states (Fin.last n) := by
  induction n with
  | zero => simp only [List.ofFn_zero, List.foldl_nil, Fin.last_zero]
  | succ n ih =>
    rw [List.ofFn_succ, List.foldl_cons]
    have hz := h 0
    change states (Fin.succ 0) = round (states 0) (parameters 0) at hz
    rw [← hz]
    exact ih (fun i => states i.succ) (fun i => parameters i.succ)
      round (fun i => h i.succ)

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
    change y ⟨1 + r.succ.val, by omega⟩ =
      poseidonFullRound (y ⟨1 + r.val, by omega⟩)
        (poseidonExternalInitial (K := K) r)
    have hidx : (⟨1 + r.succ.val, by omega⟩ : Fin 24) =
        ⟨2 + r.val, by omega⟩ := by
      apply Fin.ext
      simp only [Fin.val_mk, Fin.val_succ]
      omega
    rw [hidx]
    exact hinitial r
  have hInternal : ∀ r : Fin 14, internalStates r.succ =
      poseidonInternalRound (internalStates r.castSucc)
        (poseidonInternalConstants (K := K) r) := by
    intro r
    change y ⟨5 + r.succ.val, by omega⟩ =
      poseidonInternalRound (y ⟨5 + r.val, by omega⟩)
        (poseidonInternalConstants (K := K) r)
    have hidx : (⟨5 + r.succ.val, by omega⟩ : Fin 24) =
        ⟨6 + r.val, by omega⟩ := by
      apply Fin.ext
      simp only [Fin.val_mk, Fin.val_succ]
      omega
    rw [hidx]
    exact hinternal r
  have hFinal : ∀ r : Fin 4, finalStates r.succ =
      poseidonFullRound (finalStates r.castSucc)
        (poseidonExternalFinal (K := K) r) := by
    intro r
    change y ⟨19 + r.succ.val, by omega⟩ =
      poseidonFullRound (y ⟨19 + r.val, by omega⟩)
        (poseidonExternalFinal (K := K) r)
    have hidx : (⟨19 + r.succ.val, by omega⟩ : Fin 24) =
        ⟨20 + r.val, by omega⟩ := by
      apply Fin.ext
      simp only [Fin.val_mk, Fin.val_succ]
      omega
    rw [hidx]
    exact hfinal r
  unfold poseidonPermutation
  change (List.ofFn (poseidonExternalFinal (K := K))).foldl poseidonFullRound
      ((List.ofFn (poseidonInternalConstants (K := K))).foldl poseidonInternalRound
        ((List.ofFn (poseidonExternalInitial (K := K))).foldl poseidonFullRound
          (poseidonExternalLinear (y 0)))) = y 23
  rw [← hlead]
  have hstart : initialStates 0 = y 1 := rfl
  rw [← hstart]
  rw [foldl_compose_steps initialStates
    (poseidonExternalInitial (K := K)) poseidonFullRound hInitial]
  have hlinkInitial : initialStates (Fin.last 4) = internalStates 0 := rfl
  rw [hlinkInitial]
  rw [foldl_compose_steps internalStates
    (poseidonInternalConstants (K := K)) poseidonInternalRound hInternal]
  have hlinkInternal : internalStates (Fin.last 14) = finalStates 0 := rfl
  rw [hlinkInternal]
  rw [foldl_compose_steps finalStates
    (poseidonExternalFinal (K := K)) poseidonFullRound hFinal]
  rfl

#print axioms poseidon_chain

end R0P
