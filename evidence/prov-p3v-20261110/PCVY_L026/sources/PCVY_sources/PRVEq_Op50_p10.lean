import Aeneas
import NCV_Reference.Funs
import PCVV_LaneDecodeRef
import PRVEq_Op50_p9
open Aeneas Aeneas.Std Result ControlFlow Error
set_option autoImplicit false
noncomputable section
namespace PCVY_Op50
open PCVV_LaneDecodeRef (sl le)

theorem K0_decodeDigest : K0.decodeDigest = decDig := rfl

theorem set_take {α : Type} (l : List α) (n : Nat) (v : α) (h : n < l.length) :
    (l.set n v).take (n + 1) = l.take n ++ [v] := by
  induction l generalizing n with
  | nil => simp at h
  | cons a t ih =>
    cases n with
    | zero => simp
    | succ n =>
      have h' : n < t.length := by simpa using h
      simp only [List.set_cons_succ, List.take_succ_cons, List.cons_append, List.cons.injEq,
        true_and]
      exact ih n h'

/-! ## 7. decode_frontier_loop / decode_frontier -/

theorem frontier_loop_eq (tree : Slice U8) (hlen : 688 ≤ tree.val.length) (next : U64) :
    ∀ (k : Nat) (F : Std.Array (Std.Array U32 8#usize) 20#usize) (level : Usize),
      20 - level.val = k → level.val ≤ 20 →
      match PCVV_LaneDecodeRef.frontierLoop K0 (bytesOf tree) next.val (20 - level.val) level.val with
      | none => NCV_Reference.decode_frontier_loop tree next F level = ok (core.result.Result.Err ())
      | some rest => ∃ G : Std.Array (Std.Array U32 8#usize) 20#usize,
          NCV_Reference.decode_frontier_loop tree next F level = ok (core.result.Result.Ok G) ∧
          G.val = F.val.take level.val ++ rest := by
  intro k
  induction k with
  | zero =>
    intro F level hk hl
    have h0 : 20 - level.val = 0 := by omega
    rw [h0]
    simp only [PCVV_LaneDecodeRef.frontierLoop]
    refine ⟨F, ?_, ?_⟩
    · unfold NCV_Reference.decode_frontier_loop
      rw [loop.eq_def]
      simp only [fr_body_end tree next F level (by omega)]
    · rw [List.append_nil]
      exact (List.take_of_length_le (by rw [flen]; omega)).symm
  | succ k ih =>
    intro F level hk hl
    have hl20 : level.val < 20 := by omega
    have hk' : 20 - level.val = k + 1 := by omega
    obtain ⟨hbad, hgood⟩ := fr_body tree hlen next F level hl20
    rw [hk']
    simp only [PCVV_LaneDecodeRef.frontierLoop, K0_decodeDigest]
    cases hd : decDig (sl (bytesOf tree) (48 + 32 * level.val) (48 + 32 * level.val + 32)) with
    | none =>
      simp only []
      unfold NCV_Reference.decode_frontier_loop
      rw [loop.eq_def]
      simp only [hbad hd]
    | some val =>
      obtain ⟨hc1, hc2⟩ := hgood val hd
      by_cases hcond : ((next.val >>> level.val) &&& 1 == 0 && val != K0.emptyRoots level.val) = true
      · simp only [hcond, if_true]
        unfold NCV_Reference.decode_frontier_loop
        rw [loop.eq_def]
        simp only [hc1 hcond]
      · have hcond' : ((next.val >>> level.val) &&& 1 == 0 && val != K0.emptyRoots level.val) = false := by
          simpa using hcond
        simp only [hcond, if_false]
        obtain ⟨c, hc, hcv⟩ := add_ok level 1#usize (by scalar_tac)
        have hcv' : c.val = level.val + 1 := by rw [hcv, one_val]
        have ih' := ih (F.set level val) c (by omega) (by omega)
        have h20 : 20 - c.val = k := by omega
        rw [h20, hcv'] at ih'
        cases hr : PCVV_LaneDecodeRef.frontierLoop K0 (bytesOf tree) next.val k (level.val + 1) with
        | none =>
          rw [hr] at ih'
          simp only [] at ih'
          unfold NCV_Reference.decode_frontier_loop
          rw [loop.eq_def]
          simp only [hc2 hcond' c hc]
          unfold NCV_Reference.decode_frontier_loop at ih'
          exact ih'
        | some rest =>
          rw [hr] at ih'
          obtain ⟨G, hG, hGv⟩ := ih'
          refine ⟨G, ?_, ?_⟩
          · unfold NCV_Reference.decode_frontier_loop
            rw [loop.eq_def]
            simp only [hc2 hcond' c hc]
            unfold NCV_Reference.decode_frontier_loop at hG
            exact hG
          · rw [hGv]
            have hset : (F.set level val).val = F.val.set level.val val := rfl
            rw [hset, set_take F.val level.val val (by rw [flen]; exact hl20)]
            simp

#print axioms set_take
#print axioms frontier_loop_eq

theorem frontier_eq (tree : Slice U8) (hlen : 688 ≤ tree.val.length) (next : U64) :
    match PCVV_LaneDecodeRef.frontierLoop K0 (bytesOf tree) next.val 20 0 with
    | none => NCV_Reference.decode_frontier tree next = ok (core.result.Result.Err ())
    | some rest => ∃ G : Std.Array (Std.Array U32 8#usize) 20#usize,
        NCV_Reference.decode_frontier tree next = ok (core.result.Result.Ok G) ∧ G.val = rest := by
  have h := frontier_loop_eq tree hlen next 20
    (Array.repeat 20#usize (Array.repeat 8#usize 0#u32)) 0#usize (by simp) (by simp)
  have h0v : (0#usize).val = 0 := by simp
  simp only [h0v, Nat.sub_zero] at h
  unfold NCV_Reference.decode_frontier
  dsimp only
  cases hr : PCVV_LaneDecodeRef.frontierLoop K0 (bytesOf tree) next.val 20 0 with
  | none => rw [hr] at h; exact h
  | some rest =>
    rw [hr] at h
    obtain ⟨G, hG, hGv⟩ := h
    exact ⟨G, hG, by rw [hGv]; simp⟩

#print axioms frontier_eq
end PCVY_Op50
