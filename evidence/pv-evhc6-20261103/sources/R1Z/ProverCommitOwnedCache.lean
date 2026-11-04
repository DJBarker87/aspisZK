import R1Z.ProverCommitOwnedByteValue
set_option autoImplicit false
namespace R1Z.ProverCommitOwnedDecoder
open Aeneas Aeneas.Std Result AspisR1ProverStep8
open R0Z.FsStatement R1Z.FinalR1PBin
open R1Z.ProverCommitStepLoop (State)
open R1Z.ProverCommitStreamSource (Bytes32)

/-- Every populated cache is the preceding answer of the same finite oracle. -/
def cacheValid {n : Nat} (answers : Fin n → OracleAnswer) (state : State) : Prop :=
  ∀ c : Fin n, state.counter.val = c.val+1 → state.block = answerBytes (answers c)

theorem initial_cache {n : Nat} (answers : Fin n → OracleAnswer) : cacheValid answers initial := by
  intro c h
  have zero : initial.counter.val = 0 := by rfl
  omega

theorem wordsE_at {n : Nat} (answers : Fin n → OracleAnswer) (c : Fin n) (j : Fin 8) :
    wordsE n answers (finProdFinEquiv (c,j)) = blockW (answers c) j := by
  simp only [wordsE, Equiv.trans_apply, Equiv.arrowCongr_apply, Equiv.symm_apply_apply,
    Equiv.curry_symm_apply, Equiv.refl_apply, Function.comp_apply, Function.uncurry_apply_pair]
  rfl

/-- One successful operational read preserves the global cache correspondence
and returns the next word of wordsE. This is independent of the block count. -/
theorem next_cache {n : Nat} (answers : Fin n → OracleAnswer)
    (domain : Slice U8) (state after : State) (value : U32)
    (capacity : n < 2^64) (before : valid n state) (cache : cacheValid answers state)
    (success : prover_commit_reference.next (blockHash answers) domain state = ok (value, after)) :
    cacheValid answers after ∧ ∃ bound : position state < n*8,
      wordFin value = wordsE n answers ⟨position state, bound⟩ := by
  rw [next_factor] at success
  obtain ⟨triple, filled, rest⟩ := bind_success _ _ _ success
  rcases triple with ⟨counter, block, slot⟩
  simp only [Aeneas.Std.uncurry_apply_pair] at rest
  rcases before with ⟨counterbound, wordbound, empty⟩
  by_cases needed : state.word = 8#usize
  · have inbounds : state.counter.val < n := by
      by_contra outside
      simp only [refill, needed, if_true,
        blockHash_end answers domain state.seed state.counter (by omega), bind_tc_fail] at filled
      cases filled
    simp only [refill, needed, if_true, blockHash_at answers domain state.seed state.counter inbounds,
      bind_tc_ok] at filled
    cases filled
    rw [readBlock_byteWord _ _ (by decide)] at rest
    cases rest
    have inc := R1Z.ProverCommitStreamBytes.counter_step state.counter (by omega)
    have oldslot : state.word.val = 8 := by rw [needed]; scalar_tac
    constructor
    · intro c hc
      simp only at hc ⊢
      rw [inc] at hc
      have eq : c = ⟨state.counter.val, inbounds⟩ := Fin.ext (by change c.val = state.counter.val; omega)
      rw [eq]
    · have pos : position state = 8*state.counter.val := by unfold position; rw [oldslot]; omega
      refine ⟨by rw [pos]; omega, ?_⟩
      rw [byteWord_answer]
      have index : (⟨position state, by rw [pos]; omega⟩ : Fin (n*8)) =
          finProdFinEquiv (⟨state.counter.val, inbounds⟩, (0 : Fin 8)) := by
        apply Fin.ext
        simp only [finProdFinEquiv, Equiv.coe_fn_mk, Fin.val_zero]
        omega
      rw [index, wordsE_at]
      rfl
  · simp only [refill, needed, if_false] at filled
    cases filled
    have less : state.word.val < 8 := by scalar_tac
    have nonzero : 0 < state.counter.val := by
      by_contra h; have := empty (by omega); omega
    let c : Fin n := ⟨state.counter.val-1, by omega⟩
    have cval : c.val = state.counter.val-1 := rfl
    have cb : state.block = answerBytes (answers c) := cache c (by dsimp [c]; omega)
    rw [cb, readBlock_byteWord _ _ less] at rest
    cases rest
    constructor
    · simpa only [cacheValid, cb] using cache
    · have pos : position state = 8*c.val + state.word.val := by unfold position c; omega
      refine ⟨by rw [pos]; have := c.isLt; omega, ?_⟩
      rw [byteWord_answer]
      have index : (⟨position state, by rw [pos]; have := c.isLt; omega⟩ : Fin (n*8)) =
          finProdFinEquiv (c, ⟨state.word.val, less⟩) := by
        apply Fin.ext
        simp only [finProdFinEquiv, Equiv.coe_fn_mk]
        omega
      rw [index, wordsE_at]

#print axioms initial_cache
#print axioms wordsE_at
#print axioms next_cache
end R1Z.ProverCommitOwnedDecoder
