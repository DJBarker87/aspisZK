import R0P.CopyInputLinks

/-! Mechanical projections of the named output-copy registry entries.

These lemmas use only the selected source-order links and their declared
weights; they do not identify output commitments or establish semantic claims.
-/
set_option autoImplicit false

namespace AspisR1.OutputCopyLinks

open R0P

variable {K : Type} [Field K]

private def beforeAt (i : Fin 14) : CopyLink :=
  copyLinksBeforePositivity.get ⟨i.val, by
    have hlen : copyLinksBeforePositivity.length = 14 := rfl
    rw [hlen]
    exact i.isLt⟩

private theorem before_mem (i : Fin 14) : beforeAt i ∈ copyLinks := by
  have hm : beforeAt i ∈ copyLinksBeforePositivity := List.get_mem _ _
  exact List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inl hm)))

private theorem link_balance_pattern_funcs (pub : Public K) (A : Trace K)
    (hb : CopyLinkBalance pub A) (link : CopyLink) (hmem : link ∈ copyLinks)
    (hw : copyLinkWeight (K := K) link pub.nextPairIndex pub.variant ≠ 0) :
    copyPatternTuple (copyPatterns link.producer.pattern)
        (fun c => A (Fin.castLE (by omega) c) link.producer.row) =
      copyPatternTuple (copyPatterns link.consumer.pattern)
        (fun c => A (Fin.castLE (by omega) c) link.consumer.row) := by
  change (copyProducerTuple A link).2 = (copyConsumerTuple A link).2
  exact congrArg Prod.snd (hb link hmem hw)

private theorem copyPattern0_tuple (o : Fin 16 → K) :
    copyPatternTuple copyPattern0 o = o := by
  funext i
  fin_cases i <;> simp [copyPatternTuple, copyPattern0]

private theorem copyPattern6_tuple (o : Fin 16 → K) :
    copyPatternTuple copyPattern6 o = fun i => if i = 0 then o 0 else 0 := by
  funext i
  fin_cases i <;> simp [copyPatternTuple, copyPattern6]

private theorem copyPattern7_tuple (o : Fin 16 → K) :
    copyPatternTuple copyPattern7 o = fun i => if i = 0 then o 10 else 0 := by
  funext i
  fin_cases i <;> simp [copyPatternTuple, copyPattern7]

private theorem copyPatterns0 : copyPatterns 0 = copyPattern0 := rfl
private theorem copyPatterns6 : copyPatterns 6 = copyPattern6 := rfl
private theorem copyPatterns7 : copyPatterns 7 = copyPattern7 := rfl

private theorem before3_spec :
    beforeAt 3 = ⟨1124073475, 1, 0, ⟨443, 0, 0⟩, ⟨448, 0, 0⟩⟩ := rfl

private theorem before4_spec :
    beforeAt 4 = ⟨1124073476, 1, 0, ⟨459, 0, 0⟩, ⟨464, 0, 0⟩⟩ := rfl

private theorem before5_spec :
    beforeAt 5 = ⟨1124073477, 0, 0, ⟨491, 0, 0⟩, ⟨496, 0, 0⟩⟩ := rfl

private theorem before6_spec :
    beforeAt 6 = ⟨1124073478, 0, 0, ⟨507, 0, 0⟩, ⟨512, 0, 0⟩⟩ := rfl

private theorem before12_spec :
    beforeAt 12 = ⟨1124073484, 1, 0, ⟨460, 0, 6⟩, ⟨1010, 0, 7⟩⟩ := rfl

private theorem before13_spec :
    beforeAt 13 = ⟨1124073485, 0, 0, ⟨508, 0, 6⟩, ⟨1012, 0, 7⟩⟩ := rfl

private theorem castLE_eq_castAdd13 (i : Fin 16) :
    Fin.castLE (by omega : 16 ≤ 29) i = i.castAdd 13 := by
  apply Fin.ext
  rfl

private theorem castLE0 : Fin.castLE (by omega : 16 ≤ 29) (0 : Fin 16) = (0 : Fin 29) := by decide
private theorem castLE10 : Fin.castLE (by omega : 16 ≤ 29) (10 : Fin 16) = (10 : Fin 29) := by decide

private theorem privateTransfer_weight_one (pub : Public K) (link : CopyLink)
    (hkind : link.weightKind.val = 1)
    (hv : pub.variant = .privateTransfer) :
    copyLinkWeight (K := K) link pub.nextPairIndex pub.variant = 1 := by
  unfold copyLinkWeight
  rw [hkind]
  simp [hv]

/-- The two unconditional change-hash state continuations and the change-value
alias, projected from source-order links 5, 6, and 13. -/
theorem change_cells (pub : Public K) (A : Trace K)
    (hb : CopyLinkBalance pub A) :
    (∀ i : Fin 16, A (i.castAdd 13) 491 = A (i.castAdd 13) 496) ∧
    (∀ i : Fin 16, A (i.castAdd 13) 507 = A (i.castAdd 13) 512) ∧
      A 0 508 = A 10 1012 := by
  have balanceAt (link : CopyLink) (hmem : link ∈ copyLinks)
      (hkind : link.weightKind = 0) :
      copyPatternTuple (copyPatterns link.producer.pattern)
          (fun c => A (Fin.castLE (by omega) c) link.producer.row) =
        copyPatternTuple (copyPatterns link.consumer.pattern)
          (fun c => A (Fin.castLE (by omega) c) link.consumer.row) :=
    link_balance_pattern_funcs pub A hb link hmem
      (by simp [copyLinkWeight, hkind])
  have h5 := balanceAt (beforeAt 5) (before_mem 5) (by rw [before5_spec])
  have h6 := balanceAt (beforeAt 6) (before_mem 6) (by rw [before6_spec])
  have h13 := balanceAt (beforeAt 13) (before_mem 13) (by rw [before13_spec])
  refine ⟨?_, ?_, ?_⟩
  · intro i
    have hi := congrFun h5 i
    have hi' : A (Fin.castLE (by omega : 16 ≤ 29) i) 491 =
        A (Fin.castLE (by omega : 16 ≤ 29) i) 496 := by
      simpa only [before5_spec, copyPatterns0, copyPattern0_tuple] using hi
    simpa only [castLE_eq_castAdd13] using hi'
  · intro i
    have hi := congrFun h6 i
    have hi' : A (Fin.castLE (by omega : 16 ≤ 29) i) 507 =
        A (Fin.castLE (by omega : 16 ≤ 29) i) 512 := by
      simpa only [before6_spec, copyPatterns0, copyPattern0_tuple] using hi
    simpa only [castLE_eq_castAdd13] using hi'
  · have hi := congrFun h13 (0 : Fin 16)
    simpa only [before13_spec, copyPatterns6, copyPatterns7,
      copyPattern6_tuple, copyPattern7_tuple, if_true, castLE0, castLE10] using hi

/-- The private-transfer-only recipient-hash continuations and value alias,
projected from source-order links 3, 4, and 12. -/
theorem recipient_cells (pub : Public K) (A : Trace K)
    (hb : CopyLinkBalance pub A) (hv : pub.variant = .privateTransfer) :
    (∀ i : Fin 16, A (i.castAdd 13) 443 = A (i.castAdd 13) 448) ∧
    (∀ i : Fin 16, A (i.castAdd 13) 459 = A (i.castAdd 13) 464) ∧
      A 0 460 = A 10 1010 := by
  have balanceAt (link : CopyLink) (hmem : link ∈ copyLinks)
      (hkind : link.weightKind.val = 1) :
      copyPatternTuple (copyPatterns link.producer.pattern)
          (fun c => A (Fin.castLE (by omega) c) link.producer.row) =
        copyPatternTuple (copyPatterns link.consumer.pattern)
          (fun c => A (Fin.castLE (by omega) c) link.consumer.row) :=
    link_balance_pattern_funcs pub A hb link hmem
      (by rw [privateTransfer_weight_one pub link hkind hv]; exact one_ne_zero)
  have h3 := balanceAt (beforeAt 3) (before_mem 3) (by rw [before3_spec]; rfl)
  have h4 := balanceAt (beforeAt 4) (before_mem 4) (by rw [before4_spec]; rfl)
  have h12 := balanceAt (beforeAt 12) (before_mem 12)
    (by rw [before12_spec]; rfl)
  refine ⟨?_, ?_, ?_⟩
  · intro i
    have hi := congrFun h3 i
    have hi' : A (Fin.castLE (by omega : 16 ≤ 29) i) 443 =
        A (Fin.castLE (by omega : 16 ≤ 29) i) 448 := by
      simpa only [before3_spec, copyPatterns0, copyPattern0_tuple] using hi
    simpa only [castLE_eq_castAdd13] using hi'
  · intro i
    have hi := congrFun h4 i
    have hi' : A (Fin.castLE (by omega : 16 ≤ 29) i) 459 =
        A (Fin.castLE (by omega : 16 ≤ 29) i) 464 := by
      simpa only [before4_spec, copyPatterns0, copyPattern0_tuple] using hi
    simpa only [castLE_eq_castAdd13] using hi'
  · have hi := congrFun h12 (0 : Fin 16)
    simpa only [before12_spec, copyPatterns6, copyPatterns7,
      copyPattern6_tuple, copyPattern7_tuple, if_true, castLE0, castLE10] using hi

#print axioms change_cells
#print axioms recipient_cells

end AspisR1.OutputCopyLinks
