import R0P.CopyInputLinks

set_option autoImplicit false

namespace AspisR1.InputPairCopyLinks

open R0P

variable {K : Type} [Field K]

private def copyAfterAt (i : Fin 118) : CopyLink :=
  copyLinksAfterPositivity.get ⟨i.val, by
    have hlen : copyLinksAfterPositivity.length = 118 := rfl
    rw [hlen]
    exact i.isLt⟩

private theorem copy_after_mem (i : Fin 118) : copyAfterAt i ∈ copyLinks := by
  have hm : copyAfterAt i ∈ copyLinksAfterPositivity := List.get_mem _ _
  exact List.mem_append.mpr (Or.inr hm)

private theorem balance_pattern_funcs (pub : Public K) (A : Trace K)
    (hb : CopyLinkBalance pub A) (link : CopyLink) (hmem : link ∈ copyLinks)
    (hw : copyLinkWeight (K := K) link pub.nextPairIndex pub.variant ≠ 0) :
    copyPatternTuple (copyPatterns link.producer.pattern)
        (fun c => A (Fin.castLE (by omega) c) link.producer.row) =
      copyPatternTuple (copyPatterns link.consumer.pattern)
        (fun c => A (Fin.castLE (by omega) c) link.consumer.row) := by
  change (copyProducerTuple A link).2 = (copyConsumerTuple A link).2
  exact congrArg Prod.snd (hb link hmem hw)

private theorem copyPattern6_tuple (o : Fin 16 → K) :
    copyPatternTuple copyPattern6 o = fun i => if i.val = 0 then o 0 else 0 := by
  funext i
  fin_cases i <;> simp [copyPatternTuple, copyPattern6]

private theorem copyPattern7_tuple (o : Fin 16 → K) :
    copyPatternTuple copyPattern7 o = fun i => if i.val = 0 then o 10 else 0 := by
  funext i
  fin_cases i <;> simp [copyPatternTuple, copyPattern7]

private theorem copyPattern10_tuple (o : Fin 16 → K) : copyPatternTuple copyPattern10 o = fun i =>
    if h : i.val < 8 then
      o ⟨i.val + 8, by omega⟩ + (if i.val = 7 then (1051521018 : K) else 0)
    else 0 := by
  funext i
  fin_cases i <;> simp [copyPatternTuple, copyPattern10]

private theorem copyPattern11_tuple (o : Fin 16 → K) :
    copyPatternTuple copyPattern11 o = fun i =>
      if h : i.val < 8 then o ⟨i.val + 2, by omega⟩ else 0 := by
  funext i
  fin_cases i <;> simp [copyPatternTuple, copyPattern11]

private theorem copyPatterns6 : copyPatterns 6 = copyPattern6 := rfl
private theorem copyPatterns7 : copyPatterns 7 = copyPattern7 := rfl
private theorem copyPatterns10 : copyPatterns 10 = copyPattern10 := rfl
private theorem copyPatterns11 : copyPatterns 11 = copyPattern11 := rfl

private theorem after0_spec :
    copyAfterAt 0 = ⟨1124073490, 0, 0, ⟨64, 0, 10⟩, ⟨1017, 0, 11⟩⟩ := rfl

private theorem after1_spec :
    copyAfterAt 1 = ⟨1124073491, 0, 0, ⟨913, 0, 6⟩, ⟨1017, 1, 7⟩⟩ := rfl

theorem selected_bit (pub : Public K) (A : Trace K) (hb : CopyLinkBalance pub A) :
    A 0 913 = A 10 1017 := by
  have hw : copyLinkWeight (K := K) (copyAfterAt 1) pub.nextPairIndex pub.variant ≠ 0 := by
    simp [copyLinkWeight, after1_spec]
  have hpat := balance_pattern_funcs pub A hb (copyAfterAt 1) (copy_after_mem 1) hw
  have hpat' :
      copyPatternTuple copyPattern6 (fun c => A (Fin.castLE (by omega) c) 913) =
        copyPatternTuple copyPattern7 (fun c => A (Fin.castLE (by omega) c) 1017) := by
    simpa only [after1_spec, copyPatterns6, copyPatterns7] using hpat
  have hzero := congrFun hpat' (0 : Fin 16)
  have hleft :
      (Fin.castLE (by omega) (0 : Fin 16) : Fin 29) = 0 := by
    apply Fin.ext
    rfl
  have hright :
      (Fin.castLE (by omega) (10 : Fin 16) : Fin 29) = 10 := by
    apply Fin.ext
    rfl
  simpa only [copyPattern6_tuple, copyPattern7_tuple, Fin.val_zero,
    if_pos rfl, if_true, hleft, hright] using hzero

theorem right_cells (pub : Public K) (A : Trace K) (hb : CopyLinkBalance pub A) :
    ∀ i : Fin 8,
      A ⟨2 + i.val, by omega⟩ 1017 =
        A ⟨8 + i.val, by omega⟩ 64 +
          (if i.val = 7 then (1051521018 : K) else 0) := by
  intro i
  have hw : copyLinkWeight (K := K) (copyAfterAt 0) pub.nextPairIndex pub.variant ≠ 0 := by
    simp [copyLinkWeight, after0_spec]
  have hpat := balance_pattern_funcs pub A hb (copyAfterAt 0) (copy_after_mem 0) hw
  have hpat' :
      copyPatternTuple copyPattern10 (fun c => A (Fin.castLE (by omega) c) 64) =
        copyPatternTuple copyPattern11 (fun c => A (Fin.castLE (by omega) c) 1017) := by
    simpa only [after0_spec, copyPatterns10, copyPatterns11] using hpat
  let j : Fin 16 := ⟨i.val, by omega⟩
  have hj : j.val < 8 := i.isLt
  have hi := congrFun hpat' j
  have hindex2 :
      (Fin.castLE (by omega) (⟨j.val + 2, by omega⟩ : Fin 16) : Fin 29) =
        ⟨2 + i.val, by omega⟩ := by
    apply Fin.ext
    simp [j]
    omega
  have hindex8 :
      (Fin.castLE (by omega) (⟨j.val + 8, by omega⟩ : Fin 16) : Fin 29) =
        ⟨8 + i.val, by omega⟩ := by
    apply Fin.ext
    simp [j]
    omega
  simpa only [copyPattern10_tuple, copyPattern11_tuple, j, Fin.val_mk,
    if_pos hj, dif_pos hj, hindex2, hindex8] using hi.symm

#print axioms selected_bit
#print axioms right_cells

end AspisR1.InputPairCopyLinks
