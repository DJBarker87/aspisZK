import R0P.PositivityChain
import R0P.Semantics

/-! G8 named input-note and Merkle path registry cells.
Source C is `crates/aspis-statement/src/pool_v1/
pair_forest_copy_terminal_constants.rs`, inspection pin
`e4d68a70d3f6beb215c9f6dd418f4a2a3740c809`: patterns C:11–24,
input links C:28–39 and leaf/path links C:92–163. The fixed row functions
come from `Semantics.lean` at 26a11aee3.

The proof projects only the selected registry records. Pattern lemmas split
the sixteen lane indices with symbolic openings; row specifications split
the 24 levels (23 for nonfinal outputs). No trace, row universe, permutation
or Poseidon constant table is reduced. The only balance premise is
`CopyLinkBalance`. -/
set_option autoImplicit false
namespace R0P
variable {K : Type} [Field K]

private def copyBeforeAt (i : Fin 14) : CopyLink :=
  copyLinksBeforePositivity.get ⟨i.val, by
    have hlen : copyLinksBeforePositivity.length = 14 := rfl
    rw [hlen]
    exact i.isLt⟩

private def copyAfterAt (i : Fin 118) : CopyLink :=
  copyLinksAfterPositivity.get ⟨i.val, by
    have hlen : copyLinksAfterPositivity.length = 118 := rfl
    rw [hlen]
    exact i.isLt⟩

private theorem copy_before_mem (i : Fin 14) : copyBeforeAt i ∈ copyLinks := by
  have hm : copyBeforeAt i ∈ copyLinksBeforePositivity := List.get_mem _ _
  exact List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inl hm)))

private theorem copy_after_mem (i : Fin 118) : copyAfterAt i ∈ copyLinks := by
  have hm : copyAfterAt i ∈ copyLinksAfterPositivity := List.get_mem _ _
  exact List.mem_append.mpr (Or.inr hm)

private theorem copy_link_balance_pattern_funcs (pub : Public K) (A : Trace K)
    (hb : CopyLinkBalance pub A) (link : CopyLink) (hmem : link ∈ copyLinks)
    (hw : copyLinkWeight (K := K) link pub.nextPairIndex pub.variant ≠ 0) :
    copyPatternTuple (copyPatterns link.producer.pattern)
        (fun c => A (Fin.castLE (by omega) c) link.producer.row) =
      copyPatternTuple (copyPatterns link.consumer.pattern)
        (fun c => A (Fin.castLE (by omega) c) link.consumer.row) := by
  change
    (copyProducerTuple A link).2 = (copyConsumerTuple A link).2
  exact congrArg Prod.snd (hb link hmem hw)

private theorem copy_link_weight_one (pub : Public K) (link : CopyLink)
    (hkind : link.weightKind = 0) :
    copyLinkWeight (K := K) link pub.nextPairIndex pub.variant = 1 := by
  simp [copyLinkWeight, hkind]

private theorem copyPattern0_tuple (o : Fin 16 → K) :
    copyPatternTuple copyPattern0 o = o := by
  funext i
  fin_cases i <;> simp [copyPatternTuple, copyPattern0]

private theorem copyPattern1_tuple (o : Fin 16 → K) :
    copyPatternTuple copyPattern1 o = fun i => if i.val < 8 then o i else 0 := by
  funext i
  fin_cases i <;> simp [copyPatternTuple, copyPattern1]

private theorem copyPattern2_tuple (o : Fin 16 → K) :
    copyPatternTuple copyPattern2 o =
      fun i => if h : i.val < 6 then o ⟨i.val + 2, by omega⟩ else 0 := by
  funext i
  fin_cases i <;> simp [copyPatternTuple, copyPattern2]

private theorem copyPattern3_tuple (o : Fin 16 → K) :
    copyPatternTuple copyPattern3 o = fun i => if i.val < 6 then o i else 0 := by
  funext i
  fin_cases i <;> simp [copyPatternTuple, copyPattern3]

private theorem copyPattern4_tuple (o : Fin 16 → K) :
    copyPatternTuple copyPattern4 o = fun i => if i.val < 2 then o i else 0 := by
  funext i
  fin_cases i <;> simp [copyPatternTuple, copyPattern4]

private theorem copyPattern5_tuple (o : Fin 16 → K) :
    copyPatternTuple copyPattern5 o =
      fun i => if h : i.val < 2 then o ⟨i.val + 6, by omega⟩ else 0 := by
  funext i
  fin_cases i <;> simp [copyPatternTuple, copyPattern5]

private theorem copyPattern10_tuple (o : Fin 16 → K) :
    copyPatternTuple copyPattern10 o = fun i =>
      if h : i.val < 8 then
        o ⟨i.val + 8, by omega⟩ + (if i.val = 7 then (1051521018 : K) else 0)
      else 0 := by
  funext i
  fin_cases i <;> simp [copyPatternTuple, copyPattern10]

private theorem copyPattern12_tuple (o : Fin 16 → K) :
    copyPatternTuple copyPattern12 o =
      fun i => if h : i.val < 8 then o ⟨i.val + 1, by omega⟩ else 0 := by
  funext i
  fin_cases i <;> simp [copyPatternTuple, copyPattern12]

private theorem copyPattern13_tuple (o : Fin 16 → K) :
    copyPatternTuple copyPattern13 o =
      fun i => if h : i.val < 8 then o ⟨i.val + 8, by omega⟩ else 0 := by
  funext i
  fin_cases i <;> simp [copyPatternTuple, copyPattern13]

private theorem copyPatterns0 : copyPatterns 0 = copyPattern0 := rfl
private theorem copyPatterns1 : copyPatterns 1 = copyPattern1 := rfl
private theorem copyPatterns2 : copyPatterns 2 = copyPattern2 := rfl
private theorem copyPatterns3 : copyPatterns 3 = copyPattern3 := rfl
private theorem copyPatterns4 : copyPatterns 4 = copyPattern4 := rfl
private theorem copyPatterns5 : copyPatterns 5 = copyPattern5 := rfl
private theorem copyPatterns6 : copyPatterns 6 = copyPattern6 := rfl
private theorem copyPatterns7 : copyPatterns 7 = copyPattern7 := rfl
private theorem copyPatterns10 : copyPatterns 10 = copyPattern10 := rfl
private theorem copyPatterns12 : copyPatterns 12 = copyPattern12 := rfl
private theorem copyPatterns13 : copyPatterns 13 = copyPattern13 := rfl

private theorem copyBefore0_spec :
    copyBeforeAt 0 = ⟨1124073472, 0, 0, ⟨27, 0, 0⟩, ⟨32, 0, 0⟩⟩ := rfl
private theorem copyBefore1_spec :
    copyBeforeAt 1 = ⟨1124073473, 0, 0, ⟨43, 0, 0⟩, ⟨48, 0, 0⟩⟩ := rfl
private theorem copyBefore2_spec :
    copyBeforeAt 2 = ⟨1124073474, 0, 0, ⟨411, 0, 0⟩, ⟨416, 0, 0⟩⟩ := rfl
private theorem copyBefore7_spec :
    copyBeforeAt 7 = ⟨1124073479, 0, 0, ⟨11, 0, 1⟩, ⟨28, 0, 1⟩⟩ := rfl
private theorem copyBefore8_spec :
    copyBeforeAt 8 = ⟨1124073480, 0, 0, ⟨12, 0, 1⟩, ⟨412, 0, 1⟩⟩ := rfl
private theorem copyBefore9_spec :
    copyBeforeAt 9 = ⟨1124073481, 0, 0, ⟨44, 0, 2⟩, ⟨428, 0, 3⟩⟩ := rfl
private theorem copyBefore10_spec :
    copyBeforeAt 10 = ⟨1124073482, 0, 0, ⟨60, 0, 4⟩, ⟨428, 1, 5⟩⟩ := rfl
private theorem copyBefore11_spec :
    copyBeforeAt 11 = ⟨1124073483, 0, 0, ⟨44, 1, 6⟩, ⟨1008, 0, 7⟩⟩ := rfl
private theorem copyAfter46_spec :
    copyAfterAt 46 = ⟨1124073536, 0, 0, ⟨59, 0, 1⟩, ⟨913, 0, 12⟩⟩ := rfl

private def copyPathLeftAt (level : Fin 24) : CopyLink :=
  copyAfterAt ⟨47 + 3 * level.val, by omega⟩

private def copyPathRightAt (level : Fin 24) : CopyLink :=
  copyAfterAt ⟨48 + 3 * level.val, by omega⟩

private def copyPathOutputAt (level : Fin 23) : CopyLink :=
  copyAfterAt ⟨49 + 3 * level.val, by omega⟩

private theorem copyPathLeft_spec (level : Fin 24) :
    (copyPathLeftAt level).weightKind = 0 ∧
    (copyPathLeftAt level).producer.row = succRow (pathBaseRow level) ∧
    (copyPathLeftAt level).producer.pattern = 1 ∧
    (copyPathLeftAt level).consumer.row =
      ⟨16 * (nodeBlock level).val + 12, by omega⟩ ∧
    (copyPathLeftAt level).consumer.pattern = 1 := by
  fin_cases level <;> decide

private theorem copyPathRight_spec (level : Fin 24) :
    (copyPathRightAt level).weightKind = 0 ∧
    (copyPathRightAt level).producer.row = succRow (pathBaseRow level) ∧
    (copyPathRightAt level).producer.pattern = 13 ∧
    (copyPathRightAt level).consumer.row =
      ⟨16 * (nodeBlock level).val, by omega⟩ ∧
    (copyPathRightAt level).consumer.pattern = 10 := by
  fin_cases level <;> decide

private theorem copyPathOutput_spec (level : Fin 23) :
    (copyPathOutputAt level).weightKind = 0 ∧
    (copyPathOutputAt level).producer.row =
      ⟨16 * (nodeBlock (Fin.castLE (by omega) level)).val + 11, by omega⟩ ∧
    (copyPathOutputAt level).producer.pattern = 1 ∧
    (copyPathOutputAt level).consumer.row = pathBaseRow ⟨level.val + 1, by omega⟩ ∧
    (copyPathOutputAt level).consumer.pattern = 12 := by
  fin_cases level <;> decide

theorem copy_input_note_cells_of_balance (pub : Public K) (A : Trace K)
    (hb : CopyLinkBalance pub A) :
    (∀ i : Fin 16, A (Fin.castLE (by omega) i) 27 = A (Fin.castLE (by omega) i) 32) ∧
    (∀ i : Fin 16, A (Fin.castLE (by omega) i) 43 = A (Fin.castLE (by omega) i) 48) ∧
    (∀ i : Fin 16, A (Fin.castLE (by omega) i) 411 = A (Fin.castLE (by omega) i) 416) ∧
    (∀ i : Fin 8, A (Fin.castLE (by omega) (⟨i.val, by omega⟩ : Fin 16)) 11 = A (Fin.castLE (by omega) (⟨i.val, by omega⟩ : Fin 16)) 28) ∧
    (∀ i : Fin 8, A (Fin.castLE (by omega) (⟨i.val, by omega⟩ : Fin 16)) 12 = A (Fin.castLE (by omega) (⟨i.val, by omega⟩ : Fin 16)) 412) ∧
    (∀ i : Fin 6, A (Fin.castLE (by omega) (⟨i.val + 2, by omega⟩ : Fin 16)) 44 = A (Fin.castLE (by omega) (⟨i.val, by omega⟩ : Fin 16)) 428) ∧
    (∀ i : Fin 2, A (Fin.castLE (by omega) (⟨i.val, by omega⟩ : Fin 16)) 60 = A (Fin.castLE (by omega) (⟨i.val + 6, by omega⟩ : Fin 16)) 428) ∧
    A (Fin.castLE (by omega) (0 : Fin 16)) 44 = A (Fin.castLE (by omega) (10 : Fin 16)) 1008 ∧
    (∀ i : Fin 8, A (Fin.castLE (by omega) (⟨i.val, by omega⟩ : Fin 16)) 59 = A (Fin.castLE (by omega) (⟨i.val + 1, by omega⟩ : Fin 16)) 913) := by
  have balanceAt (link : CopyLink) (hmem : link ∈ copyLinks) (hkind : link.weightKind = 0) :
      copyPatternTuple (copyPatterns link.producer.pattern)
          (fun c => A (Fin.castLE (by omega) c) link.producer.row) =
        copyPatternTuple (copyPatterns link.consumer.pattern)
          (fun c => A (Fin.castLE (by omega) c) link.consumer.row) :=
    copy_link_balance_pattern_funcs pub A hb link hmem
      (by rw [copy_link_weight_one pub link hkind]; exact one_ne_zero)
  have h0 := balanceAt (copyBeforeAt 0) (copy_before_mem 0) (by rw [copyBefore0_spec])
  have h1 := balanceAt (copyBeforeAt 1) (copy_before_mem 1) (by rw [copyBefore1_spec])
  have h2 := balanceAt (copyBeforeAt 2) (copy_before_mem 2) (by rw [copyBefore2_spec])
  have h7 := balanceAt (copyBeforeAt 7) (copy_before_mem 7) (by rw [copyBefore7_spec])
  have h8 := balanceAt (copyBeforeAt 8) (copy_before_mem 8) (by rw [copyBefore8_spec])
  have h9 := balanceAt (copyBeforeAt 9) (copy_before_mem 9) (by rw [copyBefore9_spec])
  have h10 := balanceAt (copyBeforeAt 10) (copy_before_mem 10) (by rw [copyBefore10_spec])
  have h11 := balanceAt (copyBeforeAt 11) (copy_before_mem 11) (by rw [copyBefore11_spec])
  have h64 := balanceAt (copyAfterAt 46) (copy_after_mem 46) (by rw [copyAfter46_spec])
  constructor
  · intro i
    have hi := congrFun h0 i
    simpa only [copyBefore0_spec, copyPatterns0, copyPattern0_tuple] using hi
  constructor
  · intro i
    have hi := congrFun h1 i
    simpa only [copyBefore1_spec, copyPatterns0, copyPattern0_tuple] using hi
  constructor
  · intro i
    have hi := congrFun h2 i
    simpa only [copyBefore2_spec, copyPatterns0, copyPattern0_tuple] using hi
  constructor
  · intro i
    let j : Fin 16 := ⟨i.val, by omega⟩
    have hj : j.val < 8 := i.isLt
    have hi := congrFun h7 j
    simpa only [copyBefore7_spec, copyPatterns1, copyPattern1_tuple,
      Fin.val_mk, if_pos hj] using hi
  constructor
  · intro i
    let j : Fin 16 := ⟨i.val, by omega⟩
    have hj : j.val < 8 := i.isLt
    have hi := congrFun h8 j
    simpa only [copyBefore8_spec, copyPatterns1, copyPattern1_tuple,
      Fin.val_mk, if_pos hj] using hi
  constructor
  · intro i
    let j : Fin 16 := ⟨i.val, by omega⟩
    have hj : j.val < 6 := i.isLt
    have hi := congrFun h9 j
    simpa only [copyBefore9_spec, copyPatterns2, copyPatterns3,
      copyPattern2_tuple, copyPattern3_tuple, j, Fin.val_mk,
      if_pos hj, dif_pos hj] using hi
  constructor
  · intro i
    let j : Fin 16 := ⟨i.val, by omega⟩
    have hj : j.val < 2 := i.isLt
    have hi := congrFun h10 j
    simpa only [copyBefore10_spec, copyPatterns4, copyPatterns5,
      copyPattern4_tuple, copyPattern5_tuple, j, Fin.val_mk,
      if_pos hj, dif_pos hj] using hi
  constructor
  · have hs := (copy_singleton_patterns (K := K) (fun c => A (Fin.castLE (by omega) c) 44)).1
    have ht := (copy_singleton_patterns (K := K) (fun c => A (Fin.castLE (by omega) c) 1008)).2.1
    have h' :
        copyPatternTuple (copyPatterns 6) (fun c => A (Fin.castLE (by omega) c) 44) =
          copyPatternTuple (copyPatterns 7) (fun c => A (Fin.castLE (by omega) c) 1008) := by
      simpa only [copyBefore11_spec] using h11
    rw [hs, ht] at h'
    have h := congrFun h' 0
    simpa only [if_true] using h
  · intro i
    let j : Fin 16 := ⟨i.val, by omega⟩
    have hj : j.val < 8 := i.isLt
    have hi := congrFun h64 j
    simpa only [copyAfter46_spec, copyPatterns1, copyPatterns12,
      copyPattern1_tuple, copyPattern12_tuple, j, Fin.val_mk,
      if_pos hj, dif_pos hj] using hi

/-- The path registry links are C:93–163. For each level, the two enabled
links equate the carried digest with the left/right permutation inputs; the
right input retains the source's lane-15 offset. For nonfinal levels, the
output link carries the node digest to the next path row. -/
theorem copy_path_cells_of_balance (pub : Public K) (A : Trace K)
    (hb : CopyLinkBalance pub A) (level : Fin 24) :
    (∀ i : Fin 8,
      A (Fin.castLE (by omega) (⟨i.val, by omega⟩ : Fin 16)) (succRow (pathBaseRow level)) =
        A (Fin.castLE (by omega) (⟨i.val, by omega⟩ : Fin 16))
          ⟨16 * (nodeBlock level).val + 12, by omega⟩) ∧
    (∀ i : Fin 8,
      A (Fin.castLE (by omega) (⟨i.val + 8, by omega⟩ : Fin 16))
          (succRow (pathBaseRow level)) =
        A (Fin.castLE (by omega) (⟨i.val + 8, by omega⟩ : Fin 16))
          ⟨16 * (nodeBlock level).val, by omega⟩ +
          (if i.val = 7 then (1051521018 : K) else 0)) ∧
    (∀ hlevel : level.val < 23, ∀ i : Fin 8,
      A (Fin.castLE (by omega) (⟨i.val, by omega⟩ : Fin 16))
          ⟨16 * (nodeBlock (Fin.castLE (by omega) (⟨level.val, hlevel⟩ : Fin 23))).val + 11, by omega⟩ =
        A (Fin.castLE (by omega) (⟨i.val + 1, by omega⟩ : Fin 16))
          (pathBaseRow ⟨level.val + 1, by omega⟩)) := by
  rcases copyPathLeft_spec level with ⟨hkindL, hprodRowL, hprodPatL, hconsRowL, hconsPatL⟩
  rcases copyPathRight_spec level with ⟨hkindR, hprodRowR, hprodPatR, hconsRowR, hconsPatR⟩
  have hmemL : copyPathLeftAt level ∈ copyLinks :=
    copy_after_mem ⟨47 + 3 * level.val, by omega⟩
  have hmemR : copyPathRightAt level ∈ copyLinks :=
    copy_after_mem ⟨48 + 3 * level.val, by omega⟩
  have hweightL :
      copyLinkWeight (K := K) (copyPathLeftAt level) pub.nextPairIndex pub.variant ≠ 0 := by
    rw [copy_link_weight_one pub (copyPathLeftAt level) hkindL]
    exact one_ne_zero
  have hweightR :
      copyLinkWeight (K := K) (copyPathRightAt level) pub.nextPairIndex pub.variant ≠ 0 := by
    rw [copy_link_weight_one pub (copyPathRightAt level) hkindR]
    exact one_ne_zero
  have hleft := copy_link_balance_pattern_funcs pub A hb (copyPathLeftAt level) hmemL hweightL
  have hright := copy_link_balance_pattern_funcs pub A hb (copyPathRightAt level) hmemR hweightR
  rw [hprodRowL, hprodPatL, hconsRowL, hconsPatL] at hleft
  rw [hprodRowR, hprodPatR, hconsRowR, hconsPatR] at hright
  have hleft' :
      copyPatternTuple (copyPattern1)
        (fun c => A (Fin.castLE (by omega) c) (succRow (pathBaseRow level)) ) =
      copyPatternTuple (copyPattern1)
        (fun c => A (Fin.castLE (by omega) c) ⟨16 * (nodeBlock level).val + 12, by omega⟩) := by
    simpa only [copyPatterns1] using hleft
  have hright' :
      copyPatternTuple (copyPattern13)
        (fun c => A (Fin.castLE (by omega) c) (succRow (pathBaseRow level))) =
      copyPatternTuple (copyPattern10)
        (fun c => A (Fin.castLE (by omega) c) ⟨16 * (nodeBlock level).val, by omega⟩) := by
    simpa only [copyPatterns10, copyPatterns13] using hright
  constructor
  · intro i
    let j : Fin 16 := ⟨i.val, by omega⟩
    have hj : j.val < 8 := i.isLt
    have hi := congrFun hleft' j
    simpa only [copyPattern1_tuple, j, Fin.val_mk, if_pos hj] using hi
  constructor
  · intro i
    let j : Fin 16 := ⟨i.val, by omega⟩
    have hj : j.val < 8 := by simpa only [j, Fin.val_mk] using i.isLt
    have hi := congrFun hright' j
    simpa only [copyPattern13_tuple, copyPattern10_tuple, j, Fin.val_mk,
      if_pos hj, dif_pos hj] using hi
  · intro hlevel i
    let level23 : Fin 23 := ⟨level.val, hlevel⟩
    rcases copyPathOutput_spec level23 with
      ⟨hkindO, hprodRowO, hprodPatO, hconsRowO, hconsPatO⟩
    have hmemO : copyPathOutputAt level23 ∈ copyLinks :=
      copy_after_mem ⟨49 + 3 * level23.val, by omega⟩
    have hweightO :
        copyLinkWeight (K := K) (copyPathOutputAt level23) pub.nextPairIndex pub.variant ≠ 0 := by
      rw [copy_link_weight_one pub (copyPathOutputAt level23) hkindO]
      exact one_ne_zero
    have hout := copy_link_balance_pattern_funcs pub A hb
      (copyPathOutputAt level23) hmemO hweightO
    rw [hprodRowO, hprodPatO, hconsRowO, hconsPatO] at hout
    have hout' :
        copyPatternTuple copyPattern1
          (fun c => A (Fin.castLE (by omega) c)
            ⟨16 * (nodeBlock (Fin.castLE (by omega) level23)).val + 11, by omega⟩) =
        copyPatternTuple copyPattern12
          (fun c => A (Fin.castLE (by omega) c)
            (pathBaseRow ⟨level.val + 1, by omega⟩)) := by
      simpa only [copyPatterns1, copyPatterns12] using hout
    let j : Fin 16 := ⟨i.val, by omega⟩
    have hj : j.val < 8 := i.isLt
    have hi := congrFun hout' j
    simpa only [copyPattern1_tuple, copyPattern12_tuple, j, Fin.val_mk,
      if_pos hj, dif_pos hj] using hi

end R0P

#print axioms R0P.copyBeforeAt
#print axioms R0P.copyAfterAt
#print axioms R0P.copy_before_mem
#print axioms R0P.copy_after_mem
#print axioms R0P.copy_link_balance_pattern_funcs
#print axioms R0P.copy_link_weight_one
#print axioms R0P.copyPattern0_tuple
#print axioms R0P.copyPattern1_tuple
#print axioms R0P.copyPattern2_tuple
#print axioms R0P.copyPattern3_tuple
#print axioms R0P.copyPattern4_tuple
#print axioms R0P.copyPattern5_tuple
#print axioms R0P.copyPattern10_tuple
#print axioms R0P.copyPattern12_tuple
#print axioms R0P.copyPattern13_tuple
#print axioms R0P.copyPatterns0
#print axioms R0P.copyPatterns1
#print axioms R0P.copyPatterns2
#print axioms R0P.copyPatterns3
#print axioms R0P.copyPatterns4
#print axioms R0P.copyPatterns5
#print axioms R0P.copyPatterns6
#print axioms R0P.copyPatterns7
#print axioms R0P.copyPatterns10
#print axioms R0P.copyPatterns12
#print axioms R0P.copyPatterns13
#print axioms R0P.copyBefore0_spec
#print axioms R0P.copyBefore1_spec
#print axioms R0P.copyBefore2_spec
#print axioms R0P.copyBefore7_spec
#print axioms R0P.copyBefore8_spec
#print axioms R0P.copyBefore9_spec
#print axioms R0P.copyBefore10_spec
#print axioms R0P.copyBefore11_spec
#print axioms R0P.copyAfter46_spec
#print axioms R0P.copyPathLeftAt
#print axioms R0P.copyPathRightAt
#print axioms R0P.copyPathOutputAt
#print axioms R0P.copyPathLeft_spec
#print axioms R0P.copyPathRight_spec
#print axioms R0P.copyPathOutput_spec
#print axioms R0P.copy_input_note_cells_of_balance
#print axioms R0P.copy_path_cells_of_balance

-- Coordinator audit of the two public interfaces, in addition to their axioms.
#check @R0P.copy_input_note_cells_of_balance
#check @R0P.copy_path_cells_of_balance
