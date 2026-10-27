import R1Z.BuilderTreeCarryExtracted
import R1Z.BuilderRecordsArray
import R1Z.BuilderRecordsFields

/-! Symbolic frame and stop invariant for the owned carry. The parent callback
may be partial and stateful. No hash, canonicality, or source admission premise
is hidden in the statement. -/
set_option autoImplicit false
namespace R1Z.BuilderTreeCarry
open Aeneas Aeneas.Std Result R0Z.WriterRefine BuilderRecordsArray BuilderRecordsFields
open AspisBuilderTreeReference.pool_v1.incremental_merkle.tree_reference
abbrev Digest := Array U32 8#usize
abbrev Frontier := Array Digest 20#usize
abbrev Roots := Array Digest 21#usize
abbrev Parent (H : Type) := core.ops.function.FnMut H (Digest × Digest) Digest

def bit (index : U64) (level : Usize) : U64 :=
  BuilderStdModels.shift64 index level &&& 1#u64

theorem loop_step {H : Type} (parent : Parent H) (index : U64) (empty : Roots)
    (frontier : Frontier) (carry : Digest) (level : Usize) (state : H)
    (hl : level.val < 20) (hb : bit index level = 1#u64) :
    carry_owned_with_loop parent frontier empty carry index level state = (do
      let (next,state') ← parent.call_mut state (frontier.val[level.val]!,carry)
      carry_owned_with_loop parent (frontier.set level empty.val[level.val]!) empty next index
        (Usize.wrapping_add level 1#usize) state') := by
  rw [carry_owned_with_loop,if_pos (show level < 20#usize by simpa [UScalar.lt_equiv] using hl)]
  simp only [lift,bind_tc_ok]
  have hb' : BuilderStdModels.shift64 index level &&& 1#u64 = 1#u64 := hb
  rw [if_pos hb',index_ok_gen frontier level (by simpa using hl)]
  simp only [bind_tc_ok]
  congr 1
  funext result
  rcases result with ⟨next,state'⟩
  rw [index_ok_gen empty level (by simp; omega)]
  simp only [bind_tc_ok]
  rw [update_gen frontier level _ (by simpa using hl)]
  rfl

theorem loop_frame {H : Type} (parent : Parent H) (index : U64) (empty : Roots)
    (frontier : Frontier) (carry : Digest) (level : Usize) (state : H)
    (out : Frontier) (digest : Digest) (stop : Usize)
    (hl : level.val ≤ 20)
    (h : carry_owned_with_loop parent frontier empty carry index level state = ok (out,digest,stop)) :
    level.val ≤ stop.val ∧ stop.val ≤ 20 ∧
      (stop.val = 20 ∨ bit index stop ≠ 1#u64) ∧
      ∀ j, j < 20 → out.val[j]! =
        if level.val ≤ j ∧ j < stop.val then empty.val[j]! else frontier.val[j]! := by
  generalize he : 20-level.val = remaining
  induction remaining using Nat.strong_induction_on generalizing frontier carry level state out digest stop with
  | h remaining ih =>
    rw [carry_owned_with_loop] at h
    by_cases hlt : level.val < 20
    · rw [if_pos (show level < 20#usize by simpa [UScalar.lt_equiv] using hlt)] at h
      simp only [lift,bind_tc_ok] at h
      by_cases hb : BuilderStdModels.shift64 index level &&& 1#u64 = 1#u64
      · rw [if_pos hb] at h
        rw [index_ok_gen frontier level (by simpa using hlt)] at h
        simp only [bind_tc_ok] at h
        obtain ⟨⟨next,state'⟩,_,h⟩ := bind_ok_inv h
        rw [index_ok_gen empty level (by simp; omega)] at h
        simp only [bind_tc_ok] at h
        rw [update_gen frontier level _ (by simpa using hlt)] at h
        simp only [bind_tc_ok,lift] at h
        have hn : (Usize.wrapping_add level 1#usize).val = level.val+1 := by
          rw [uadd _ _ (by simp; omega)]; rfl
        obtain ⟨hstart,hstop,hbit,hframe⟩ := ih
          (20-(Usize.wrapping_add level 1#usize).val) (by omega)
          (frontier.set level empty.val[level.val]!) next (Usize.wrapping_add level 1#usize)
          state' out digest stop (by omega) h rfl
        refine ⟨by omega,hstop,hbit,?_⟩
        intro j hj
        rw [hframe j hj,BuilderRecordsArray.set_get _ _ _ _ (by simpa using hlt)]
        split_ifs <;> first | rfl | (exfalso; omega) | (congr 1 <;> omega)
      · rw [if_neg hb] at h
        obtain ⟨rfl,rfl,rfl⟩ := Prod.mk.inj (Result.ok.inj h)
        refine ⟨le_rfl,hl,Or.inr hb,?_⟩
        intro j hj
        rw [if_neg (by omega)]
    · rw [if_neg (show ¬level < 20#usize by simpa [UScalar.lt_equiv] using hlt)] at h
      obtain ⟨rfl,rfl,rfl⟩ := Prod.mk.inj (Result.ok.inj h)
      refine ⟨le_rfl,hl,Or.inl (by omega),?_⟩
      intro j hj
      rw [if_neg (by omega)]

theorem reference_frame {H : Type} (parent : Parent H) (index : U64) (empty : Roots)
    (frontier : Frontier) (leaf : Digest) (state : H)
    (out : Frontier) (digest : Digest) (stop : Usize)
    (h : carry_owned_with parent frontier empty leaf index 0#usize state = ok (out,digest,stop)) :
    stop.val ≤ 20 ∧ (stop.val = 20 ∨ bit index stop ≠ 1#u64) ∧
      ∀ j, j < 20 → out.val[j]! = if j < stop.val then empty.val[j]! else frontier.val[j]! := by
  obtain ⟨_,hs,hb,hf⟩ := loop_frame parent index empty frontier leaf 0#usize state out digest stop (by simp) h
  refine ⟨hs,hb,?_⟩
  intro j hj
  simpa using hf j hj

theorem reference_untouched {H : Type} (parent : Parent H) (index : U64) (empty : Roots)
    (frontier : Frontier) (leaf : Digest) (state : H)
    (out : Frontier) (digest : Digest) (stop : Usize)
    (h : carry_owned_with parent frontier empty leaf index 0#usize state = ok (out,digest,stop))
    (j : Nat) (hj : j < 20) (hs : stop.val ≤ j) : out.val[j]! = frontier.val[j]! := by
  have hf := (reference_frame parent index empty frontier leaf state out digest stop h).2.2 j hj
  simpa only [if_neg (show ¬j < stop.val by omega)] using hf

#print axioms loop_step
#print axioms loop_frame
#print axioms reference_frame
#print axioms reference_untouched
end R1Z.BuilderTreeCarry
