import R0P.CopyInputLinks

set_option autoImplicit false

namespace AspisR1.PairCopyLinks

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

private theorem weight_one (pub : Public K) (link : CopyLink)
    (hkind : link.weightKind = 0) :
    copyLinkWeight (K := K) link pub.nextPairIndex pub.variant = 1 := by
  simp [copyLinkWeight, hkind]

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

private theorem copyPattern11_tuple (o : Fin 16 → K) :
    copyPatternTuple copyPattern11 o = fun i =>
      if h : i.val < 8 then o ⟨i.val + 2, by omega⟩ else 0 := by
  funext i
  fin_cases i <;> simp [copyPatternTuple, copyPattern11]

private theorem copyPatterns1 : copyPatterns 1 = copyPattern1 := rfl
private theorem copyPatterns10 : copyPatterns 10 = copyPattern10 := rfl
private theorem copyPatterns11 : copyPatterns 11 = copyPattern11 := rfl

private theorem after2_spec :
    copyAfterAt 2 = ⟨1124073492, 1, 0, ⟨523, 0, 1⟩, ⟨1018, 0, 11⟩⟩ := rfl
private theorem after3_spec :
    copyAfterAt 3 = ⟨1124073493, 1, 0, ⟨475, 0, 1⟩, ⟨540, 0, 1⟩⟩ := rfl
private theorem after4_spec :
    copyAfterAt 4 = ⟨1124073494, 2, 0, ⟨523, 1, 1⟩, ⟨540, 1, 1⟩⟩ := rfl
private theorem after5_spec :
    copyAfterAt 5 = ⟨1124073495, 0, 0, ⟨1018, 0, 11⟩, ⟨528, 0, 10⟩⟩ := rfl

private theorem fin8_fin29 (i : Fin 8) :
    (Fin.castLE (by omega) (⟨i.val, by omega⟩ : Fin 16) : Fin 29) =
      i.castAdd 21 := by
  apply Fin.ext
  rfl

private theorem fin8_fin29_add2 (i : Fin 8) :
    (Fin.castLE (by omega) (⟨i.val + 2, by omega⟩ : Fin 16) : Fin 29) =
      ⟨2 + i.val, by omega⟩ := by
  apply Fin.ext
  change i.val + 2 = 2 + i.val
  omega

private theorem fin8_fin29_add8 (i : Fin 8) :
    (Fin.castLE (by omega) (⟨i.val + 8, by omega⟩ : Fin 16) : Fin 29) =
      ⟨8 + i.val, by omega⟩ := by
  apply Fin.ext
  change i.val + 8 = 8 + i.val
  omega

theorem right_cells (pub : Public K) (A : Trace K) (hb : CopyLinkBalance pub A) :
    ∀ i : Fin 8,
      A ⟨2 + i.val, by omega⟩ 1018 =
        A ⟨8 + i.val, by omega⟩ 528 +
          (if i.val = 7 then (1051521018 : K) else 0) := by
  intro i
  have hw : copyLinkWeight (K := K) (copyAfterAt 5) pub.nextPairIndex pub.variant ≠ 0 := by
    simp [copyLinkWeight, after5_spec]
  have hpat := balance_pattern_funcs pub A hb (copyAfterAt 5) (copy_after_mem 5) hw
  have hpat' :
      copyPatternTuple copyPattern11
          (fun c => A (Fin.castLE (by omega) c) 1018) =
        copyPatternTuple copyPattern10
          (fun c => A (Fin.castLE (by omega) c) 528) := by
    simpa only [after5_spec, copyPatterns1, copyPatterns10, copyPatterns11] using hpat
  let j : Fin 16 := ⟨i.val, by omega⟩
  have hj : j.val < 8 := i.isLt
  have hi := congrFun hpat' j
  have hindex2 :
      (Fin.castLE (by omega) (⟨j.val + 2, by omega⟩ : Fin 16) : Fin 29) =
        ⟨2 + i.val, by omega⟩ := by
    simpa [j] using fin8_fin29_add2 i
  have hindex8 :
      (Fin.castLE (by omega) (⟨j.val + 8, by omega⟩ : Fin 16) : Fin 29) =
        ⟨8 + i.val, by omega⟩ := by
    simpa [j] using fin8_fin29_add8 i
  simpa only [copyPattern11_tuple, copyPattern10_tuple, j, Fin.val_mk,
    if_pos hj, dif_pos hj, hindex2, hindex8] using hi

theorem first_transfer (pub : Public K) (A : Trace K) (hb : CopyLinkBalance pub A)
    (hvariant : pub.variant = .privateTransfer) :
    ∀ i : Fin 8, A (i.castAdd 21) 475 = A (i.castAdd 21) 540 := by
  intro i
  have hw : copyLinkWeight (K := K) (copyAfterAt 3) pub.nextPairIndex pub.variant ≠ 0 := by
    simp [copyLinkWeight, after3_spec, hvariant]
  have hpat := balance_pattern_funcs pub A hb (copyAfterAt 3) (copy_after_mem 3) hw
  have hpat' :
      copyPatternTuple copyPattern1
          (fun c => A (Fin.castLE (by omega) c) 475) =
        copyPatternTuple copyPattern1
          (fun c => A (Fin.castLE (by omega) c) 540) := by
    simpa only [after3_spec, copyPatterns1] using hpat
  let j : Fin 16 := ⟨i.val, by omega⟩
  have hj : j.val < 8 := i.isLt
  have hi := congrFun hpat' j
  have hindex : (Fin.castLE (by omega) j : Fin 29) = i.castAdd 21 := by
    simpa [j] using fin8_fin29 i
  simpa only [copyPattern1_tuple, j, Fin.val_mk, if_pos hj, hindex] using hi

theorem first_withdrawal (pub : Public K) (A : Trace K) (hb : CopyLinkBalance pub A)
    (hvariant : pub.variant = .withdrawal) :
    ∀ i : Fin 8, A (i.castAdd 21) 523 = A (i.castAdd 21) 540 := by
  intro i
  have hw : copyLinkWeight (K := K) (copyAfterAt 4) pub.nextPairIndex pub.variant ≠ 0 := by
    simp [copyLinkWeight, after4_spec, hvariant]
  have hpat := balance_pattern_funcs pub A hb (copyAfterAt 4) (copy_after_mem 4) hw
  have hpat' :
      copyPatternTuple copyPattern1
          (fun c => A (Fin.castLE (by omega) c) 523) =
        copyPatternTuple copyPattern1
          (fun c => A (Fin.castLE (by omega) c) 540) := by
    simpa only [after4_spec, copyPatterns1] using hpat
  let j : Fin 16 := ⟨i.val, by omega⟩
  have hj : j.val < 8 := i.isLt
  have hi := congrFun hpat' j
  have hindex : (Fin.castLE (by omega) j : Fin 29) = i.castAdd 21 := by
    simpa [j] using fin8_fin29 i
  simpa only [copyPattern1_tuple, j, Fin.val_mk, if_pos hj, hindex] using hi

theorem second_transfer (pub : Public K) (A : Trace K) (hb : CopyLinkBalance pub A)
    (hvariant : pub.variant = .privateTransfer) :
    ∀ i : Fin 8,
      A (i.castAdd 21) 523 = A ⟨2 + i.val, by omega⟩ 1018 := by
  intro i
  have hw : copyLinkWeight (K := K) (copyAfterAt 2) pub.nextPairIndex pub.variant ≠ 0 := by
    simp [copyLinkWeight, after2_spec, hvariant]
  have hpat := balance_pattern_funcs pub A hb (copyAfterAt 2) (copy_after_mem 2) hw
  have hpat' :
      copyPatternTuple copyPattern1
          (fun c => A (Fin.castLE (by omega) c) 523) =
        copyPatternTuple copyPattern11
          (fun c => A (Fin.castLE (by omega) c) 1018) := by
    simpa only [after2_spec, copyPatterns1, copyPatterns11] using hpat
  let j : Fin 16 := ⟨i.val, by omega⟩
  have hj : j.val < 8 := i.isLt
  have hi := congrFun hpat' j
  have hindex2 :
      (Fin.castLE (by omega) (⟨j.val + 2, by omega⟩ : Fin 16) : Fin 29) =
        ⟨2 + i.val, by omega⟩ := by
    simpa [j] using fin8_fin29_add2 i
  simpa only [copyPattern1_tuple, copyPattern11_tuple, j, Fin.val_mk,
    if_pos hj, dif_pos hj, hindex2, fin8_fin29] using hi

#print axioms right_cells
#print axioms first_transfer
#print axioms first_withdrawal
#print axioms second_transfer

end AspisR1.PairCopyLinks
