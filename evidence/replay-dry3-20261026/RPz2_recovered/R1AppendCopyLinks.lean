import R0P.CopyInputLinks
import R0P.Digest

/-! Mechanical projection of the two append-continuation copy-link families.
The result records only the literal copy-link consequences under their
source-declared bit weights. -/
set_option autoImplicit false

namespace AspisR1.AppendCopyLinks

open R0P

variable {K : Type} [Field K]

private def afterAt (i : Fin 118) : CopyLink :=
  copyLinksAfterPositivity.get ⟨i.val, by
    have hlen : copyLinksAfterPositivity.length = 118 := rfl
    rw [hlen]
    exact i.isLt⟩

private theorem after_mem (i : Fin 118) : afterAt i ∈ copyLinks := by
  have hm : afterAt i ∈ copyLinksAfterPositivity := List.get_mem _ _
  exact List.mem_append.mpr (Or.inr hm)

private theorem link_balance_pattern_funcs (pub : Public K) (A : Trace K)
    (hb : CopyLinkBalance pub A) (link : CopyLink) (hmem : link ∈ copyLinks)
    (hw : copyLinkWeight (K := K) link pub.nextPairIndex pub.variant ≠ 0) :
    copyPatternTuple (copyPatterns link.producer.pattern)
        (fun c => A (Fin.castLE (by omega) c) link.producer.row) =
      copyPatternTuple (copyPatterns link.consumer.pattern)
        (fun c => A (Fin.castLE (by omega) c) link.consumer.row) := by
  change (copyProducerTuple A link).2 = (copyConsumerTuple A link).2
  exact congrArg Prod.snd (hb link hmem hw)

private theorem copyPattern1_tuple (o : Fin 16 → K) :
    copyPatternTuple copyPattern1 o = fun i => if i.val < 8 then o i else 0 := by
  funext i
  fin_cases i <;> simp [copyPatternTuple, copyPattern1]

private theorem copyPattern10_tuple (o : Fin 16 → K) :
    copyPatternTuple copyPattern10 o = fun i =>
      if h : i.val < 8 then
        o ⟨i.val + 8, by omega⟩ + (if i.val = 7 then (1051521018 : K) else 0)
      else 0 := by
  funext i
  fin_cases i <;> simp [copyPatternTuple, copyPattern10]

private theorem copyPatterns1 : copyPatterns 1 = copyPattern1 := rfl
private theorem copyPatterns10 : copyPatterns 10 = copyPattern10 := rfl

private theorem leftSpec (level : Fin 20) :
    afterAt ⟨6 + 2 * level.val, by omega⟩ =
      ⟨1124073496 + 2 * level.val, 3, level.val,
        ⟨⟨539 + 16 * level.val, by omega⟩, 0, 1⟩,
        ⟨⟨556 + 16 * level.val, by omega⟩, 0, 1⟩⟩ := by
  fin_cases level <;> rfl

private theorem rightSpec (level : Fin 20) :
    afterAt ⟨7 + 2 * level.val, by omega⟩ =
      ⟨1124073497 + 2 * level.val, 4, level.val,
        ⟨⟨539 + 16 * level.val, by omega⟩, 1, 1⟩,
        ⟨⟨544 + 16 * level.val, by omega⟩, 0, 10⟩⟩ := by
  fin_cases level <;> rfl

private theorem leftRow (level : Fin 20) :
    g2Row ⟨33 + level.val, by omega⟩ 11 =
      (⟨539 + 16 * level.val, by omega⟩ : Fin 1024) := by
  apply Fin.ext
  change 16 * (33 + level.val) + 11 = 539 + 16 * level.val
  omega

private theorem rightRow12 (level : Fin 20) :
    g2Row ⟨34 + level.val, by omega⟩ 12 =
      (⟨556 + 16 * level.val, by omega⟩ : Fin 1024) := by
  apply Fin.ext
  change 16 * (34 + level.val) + 12 = 556 + 16 * level.val
  omega

private theorem rightRow0 (level : Fin 20) :
    g2Row ⟨34 + level.val, by omega⟩ 0 =
      (⟨544 + 16 * level.val, by omega⟩ : Fin 1024) := by
  apply Fin.ext
  change 16 * (34 + level.val) + 0 = 544 + 16 * level.val
  omega

private theorem castLE_fin8 (i : Fin 8) :
    Fin.castLE (by omega : 16 ≤ 29) (i.castAdd 8) = i.castAdd 21 := by
  apply Fin.ext
  rfl

private theorem castLE_fin8_shift (i : Fin 8) :
    Fin.castLE (by omega : 16 ≤ 29) ⟨i.val + 8, by omega⟩ =
      ⟨8 + i.val, by omega⟩ := by
  apply Fin.ext
  change i.val + 8 = 8 + i.val
  omega

/-- The append continuation cells selected by the zero/one branch weights in
the exact `copyLinksAfterPositivity` registry entries. -/
theorem append_cells (pub : Public K) (A : Trace K)
    (hb : CopyLinkBalance pub A) (level : Fin 20) :
    ((((pub.nextPairIndex >>> level.val) &&& 1) = 0) →
      ∀ i : Fin 8,
        A (i.castAdd 21) (g2Row ⟨33 + level.val, by omega⟩ 11) =
          A (i.castAdd 21) (g2Row ⟨34 + level.val, by omega⟩ 12)) ∧
    ((((pub.nextPairIndex >>> level.val) &&& 1) = 1) →
      ∀ i : Fin 8,
        A (i.castAdd 21) (g2Row ⟨33 + level.val, by omega⟩ 11) =
          A ⟨8 + i.val, by omega⟩ (g2Row ⟨34 + level.val, by omega⟩ 0) +
            (if i.val = 7 then (1051521018 : K) else 0)) := by
  constructor
  · intro hbit i
    have hlink := link_balance_pattern_funcs pub A hb
      (afterAt ⟨6 + 2 * level.val, by omega⟩)
      (after_mem _)
      (by simp [copyLinkWeight, leftSpec, hbit])
    have hi := congrFun hlink (i.castAdd 8)
    simpa only [leftSpec, copyPatterns1, copyPattern1_tuple,
      Fin.val_castAdd, if_pos i.isLt, castLE_fin8,
      leftRow, rightRow12] using hi
  · intro hbit i
    have hlink := link_balance_pattern_funcs pub A hb
      (afterAt ⟨7 + 2 * level.val, by omega⟩)
      (after_mem _)
      (by simp [copyLinkWeight, rightSpec, hbit])
    have hi := congrFun hlink (i.castAdd 8)
    simp only [rightSpec, copyPatterns1, copyPatterns10,
      copyPattern1_tuple, copyPattern10_tuple, Fin.val_castAdd,
      if_pos i.isLt, dif_pos i.isLt, castLE_fin8, castLE_fin8_shift] at hi
    rw [leftRow, rightRow0]
    convert hi using 1
    congr 1 <;> norm_num

#print axioms append_cells

end AspisR1.AppendCopyLinks
