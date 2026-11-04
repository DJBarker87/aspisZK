import R0Z.BuilderModel
import R0P.Schedule

/-! Builder model, block families (t2b2b/DESIGN-BUILDER-MODEL.txt §4):
`poseidonScalarFamily` holds on every layout by construction (local rows
1..11 ARE the canonical transitions); `scheduleFamily` holds on the model
because of the block roles chosen in Stage W (sponge initial states, node
pre-states, absorption supports).  The Rust-side content of both is the
refinement obligation that permute_optimized_with_trace / write_sponge /
write_node produce exactly these rows (design §6). -/
set_option autoImplicit false
noncomputable section

namespace R0Z.BuilderModel
open R0P

variable {K : Type} [Field K]

theorem layout_block' (C : Cells K) (c : Fin 29) (hc : c.val < 16) (h : Fin 57) (l : Nat)
    (hl : l < 16) (r : Fin 1024) (hr : r.val = 16 * h.val + l) :
    layout C c r = blockCell (C.blocks h) l ⟨c.val, hc⟩ := by
  rw [layout_block C c r hc h (by omega), show r.val % 16 = l by omega]

theorem state_layout (C : Cells K) (block : Fin 57) (r : Fin 16) :
    poseidonState (layout C) block r = fun lane => blockCell (C.blocks block) r.val lane := by
  funext lane
  exact layout_block' C _ lane.isLt block r.val r.isLt _ rfl

theorem blockCell_fun_iter (b : BlockIn K) (l : Nat) (hl : l < 12) :
    (fun lane => blockCell b l lane) = blockIter b l := by
  funext lane
  unfold blockCell
  rw [if_pos hl]

theorem blockCell_fun_absorb (b : BlockIn K) :
    (fun lane => blockCell b 12 lane) = b.absorb := by
  funext lane
  unfold blockCell
  rw [if_neg (by omega), if_pos rfl]

/-- Poseidon holds on every layout: rows 1..11 are the transitions. -/
theorem poseidon_layout (pub : Public K) (C : Cells K) :
    Holds poseidonScalarFamily pub (layout C) := by
  rw [poseidon_scalar_holds_iff]
  intro block row lane
  rw [state_layout, state_layout, state_layout]
  show blockCell (C.blocks block) (row.val + 1) lane =
    poseidonTransition row (fun l => blockCell (C.blocks block) row.val l)
      (fun l => blockCell (C.blocks block) 12 l) lane
  rw [blockCell_fun_iter _ row.val (by omega), blockCell_fun_absorb]
  unfold blockCell
  rw [if_pos (by omega), blockIter.eq_2, dif_pos row.isLt]

theorem poseidon_model (pub : Public K) (w : ModelWitness K) :
    Holds poseidonScalarFamily pub (buildModel pub w) :=
  poseidon_layout pub _

/-! ### Schedule -/

theorem row_cell (C : Cells K) (b : Fin 1024) (h57 : b.val / 16 < 57) (c : Fin 16) :
    layout C (c.castAdd 13) b = blockCell (C.blocks ⟨b.val / 16, h57⟩) (b.val % 16) c :=
  layout_block C _ b c.isLt ⟨b.val / 16, h57⟩ rfl

theorem nodeIn_pre_lo (l r : Digest K) (c : Fin 16) (hc : c.val < 8) : (nodeIn l r).pre c = 0 := by
  unfold nodeIn
  exact if_pos hc

theorem blockCell_pre (b : BlockIn K) (c : Fin 16) : blockCell b 0 c = b.pre c := rfl

attribute [local irreducible] blockOut blockIter blockDigest treeCur appCur

theorem blocksOf_tree_lo (pub : Public K) (w : ModelWitness K) (h : Fin 57) (h4 : 4 ≤ h.val)
    (h24 : h.val ≤ 24) :
    blocksOf pub w h = treeNode w (treeCur w (inputLeaf pub w) (h.val - 4)) ⟨h.val - 4, by omega⟩ := by
  rw [blocksOf, if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
    dif_pos h24]

theorem blocksOf_recip (pub : Public K) (w : ModelWitness K) (h : Fin 57) (h27 : 27 ≤ h.val)
    (h29 : h.val ≤ 29) : blocksOf pub w h = recipB pub w (h.val - 27) := by
  rw [blocksOf, if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
    dif_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos h29]

theorem blocksOf_app (pub : Public K) (w : ModelWitness K) (h : Fin 57) (h34 : 34 ≤ h.val)
    (h53 : h.val ≤ 53) :
    blocksOf pub w h = appNode pub (appCur pub (outPair pub w) (h.val - 34)) ⟨h.val - 34, by omega⟩ := by
  rw [blocksOf, if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
    dif_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
    if_neg (by omega), if_neg (by omega), if_neg (by omega), dif_pos h53]

theorem blocksOf_tree_hi (pub : Public K) (w : ModelWitness K) (h : Fin 57) (h54 : 54 ≤ h.val) :
    blocksOf pub w h = treeNode w (treeCur w (inputLeaf pub w) (h.val - 33))
      ⟨h.val - 33, by have := h.isLt; omega⟩ := by
  rw [blocksOf, if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
    dif_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
    if_neg (by omega), if_neg (by omega), if_neg (by omega), dif_neg (by omega)]

theorem outPairB_node (pub : Public K) (w : ModelWitness K) :
    ∃ l r : Digest K, outPairB pub w = nodeIn l r := by
  rw [outPairB]
  cases pub.variant
  · exact ⟨_, _, rfl⟩
  · exact ⟨_, _, rfl⟩

/-- Every node-role block (4..24, 33..56) is a node block. -/
theorem blocksOf_node (pub : Public K) (w : ModelWitness K) (h : Fin 57)
    (hn : ScheduleNode h.val) : ∃ l r : Digest K, blocksOf pub w h = nodeIn l r := by
  have h57 := h.isLt
  unfold ScheduleNode at hn
  by_cases ha : h.val ≤ 24
  · rw [blocksOf_tree_lo pub w h (by omega) ha]; exact ⟨_, _, rfl⟩
  · by_cases hb : h.val = 33
    · rw [show h = 33 from Fin.ext hb]; exact outPairB_node pub w
    · by_cases hc : h.val ≤ 53
      · rw [blocksOf_app pub w h (by omega) hc]; exact ⟨_, _, rfl⟩
      · rw [blocksOf_tree_hi pub w h (by omega)]; exact ⟨_, _, rfl⟩

/-- Row-12 lanes 8..15 vanish. -/
def HiZero (b : BlockIn K) : Prop := ∀ c : Fin 16, 8 ≤ c.val → b.absorb c = 0

theorem hiZero_lo8 (pre : Fin 16 → K) (d : Digest K) : HiZero (⟨pre, lo8 d⟩ : BlockIn K) := by
  intro c hc
  show lo8 d c = 0
  unfold lo8
  rw [dif_neg (by omega)]

theorem hiZero_node (l r : Digest K) : HiZero (nodeIn l r) := hiZero_lo8 _ _

theorem hiZero_noteB1 (o : Digest K) (v a : K) (s : Digest K) : HiZero (noteB1 o v a s) := by
  intro c hc
  show noteC2 v a s c = 0
  unfold noteC2
  rw [if_neg (by omega), if_neg (by omega), dif_neg (by omega)]

theorem noteC3_zero (s : Digest K) (c : Fin 16) (hc : 2 ≤ c.val) : noteC3 s c = 0 := by
  unfold noteC3
  rw [if_neg (by omega), if_neg (by omega)]

theorem hiZero_noteB2 (o : Digest K) (v a : K) (s : Digest K) : HiZero (noteB2 o v a s) :=
  fun c hc => noteC3_zero s c (by omega)

theorem hiZero_recipB (pub : Public K) (w : ModelWitness K) (j : Nat) : HiZero (recipB pub w j) := by
  rw [recipB]
  cases pub.variant
  · by_cases h0 : j = 0
    · rw [if_pos h0]; exact hiZero_lo8 _ _
    · by_cases h1 : j = 1
      · rw [if_neg h0, if_pos h1]; exact hiZero_noteB1 _ _ _ _
      · rw [if_neg h0, if_neg h1]; exact hiZero_noteB2 _ _ _ _
  · exact fun _ _ => rfl

theorem blocksOf_hiZero (pub : Public K) (w : ModelWitness K) (h : Fin 57) :
    HiZero (blocksOf pub w h) := by
  have h57 := h.isLt
  have hcase : h.val = 0 ∨ h.val = 1 ∨ h.val = 2 ∨ h.val = 3 ∨ (4 ≤ h.val ∧ h.val ≤ 24) ∨
      h.val = 25 ∨ h.val = 26 ∨ (27 ≤ h.val ∧ h.val ≤ 29) ∨ h.val = 30 ∨ h.val = 31 ∨
      h.val = 32 ∨ h.val = 33 ∨ (34 ≤ h.val ∧ h.val ≤ 53) ∨ 54 ≤ h.val := by omega
  rcases hcase with e | e | e | e | ⟨e1, e2⟩ | e | e | ⟨e1, e2⟩ | e | e | e | e | ⟨e1, e2⟩ | e
  · rw [show h = 0 from Fin.ext e]; exact hiZero_lo8 _ _
  · rw [show h = 1 from Fin.ext e]; exact hiZero_lo8 _ _
  · rw [show h = 2 from Fin.ext e]; exact hiZero_noteB1 _ _ _ _
  · rw [show h = 3 from Fin.ext e]; exact hiZero_noteB2 _ _ _ _
  · rw [blocksOf_tree_lo pub w h e1 e2]; exact hiZero_node _ _
  · rw [show h = 25 from Fin.ext e]; exact hiZero_lo8 _ _
  · rw [show h = 26 from Fin.ext e]; exact hiZero_lo8 _ _
  · rw [blocksOf_recip pub w h e1 e2]; exact hiZero_recipB pub w _
  · rw [show h = 30 from Fin.ext e]; exact hiZero_lo8 _ _
  · rw [show h = 31 from Fin.ext e]; exact hiZero_noteB1 _ _ _ _
  · rw [show h = 32 from Fin.ext e]; exact hiZero_noteB2 _ _ _ _
  · rw [show h = 33 from Fin.ext e]
    obtain ⟨l, r, hlr⟩ := outPairB_node pub w
    show HiZero (outPairB pub w)
    rw [hlr]; exact hiZero_node _ _
  · rw [blocksOf_app pub w h e1 e2]; exact hiZero_node _ _
  · rw [blocksOf_tree_hi pub w h e]; exact hiZero_node _ _

theorem recipB_wd (pub : Public K) (w : ModelWitness K) (j : Nat) (hv : pub.variant = .withdrawal) :
    recipB pub w j = ⟨0, 0⟩ := by
  rw [recipB, hv]

/-- Absorption support, ScheduleAbsorbs (Schedule.lean:91). -/
theorem blocksOf_absorb_zero (pub : Public K) (w : ModelWitness K) (h : Fin 57) (c : Fin 16)
    (ha : ScheduleAbsorbs pub.variant h.val c.val) : (blocksOf pub w h).absorb c = 0 := by
  unfold ScheduleAbsorbs at ha
  by_cases h2 : c.val < 2
  · rw [if_pos h2] at ha
    obtain ⟨hv, e | e | e⟩ := ha
    · rw [show h = 27 from Fin.ext e]
      show (recipB pub w 0).absorb c = 0
      rw [recipB_wd pub w 0 hv]; rfl
    · rw [show h = 28 from Fin.ext e]
      show (recipB pub w 1).absorb c = 0
      rw [recipB_wd pub w 1 hv]; rfl
    · rw [show h = 29 from Fin.ext e]
      show (recipB pub w 2).absorb c = 0
      rw [recipB_wd pub w 2 hv]; rfl
  · rw [if_neg h2] at ha
    by_cases h8 : c.val < 8
    · rw [if_pos h8] at ha
      rcases ha with e | e | e | ⟨hv, e | e⟩
      · rw [show h = 3 from Fin.ext e]
        exact noteC3_zero _ c (by omega)
      · rw [show h = 32 from Fin.ext e]
        exact noteC3_zero _ c (by omega)
      · rw [show h = 29 from Fin.ext e]
        show (recipB pub w 2).absorb c = 0
        rw [recipB]
        split
        · exact noteC3_zero _ c (by omega)
        · rfl
      · rw [show h = 27 from Fin.ext e]
        show (recipB pub w 0).absorb c = 0
        rw [recipB_wd pub w 0 hv]; rfl
      · rw [show h = 28 from Fin.ext e]
        show (recipB pub w 1).absorb c = 0
        rw [recipB_wd pub w 1 hv]; rfl
    · exact blocksOf_hiZero pub w h c (by omega)

theorem schedule_model (pub : Public K) (w : ModelWitness K) :
    Holds scheduleFamily pub (buildModel pub w) := by
  rw [schedule_holds_iff]
  refine ⟨?_, ?_, ?_⟩
  · intro b hb hf c
    have h57 : b.val / 16 < 57 := by unfold ScheduleFull at hf; omega
    rw [buildModel, row_cell _ b h57 c, hb, blockCell_pre]
    show (blocksOf pub w ⟨b.val / 16, h57⟩).pre c = _
    unfold ScheduleFull at hf
    rcases hf with e | e | e | e | e | ⟨hv, e | e⟩
    · rw [show (⟨b.val / 16, h57⟩ : Fin 57) = 0 from Fin.ext e, e]
      fin_cases c <;> rfl
    · rw [show (⟨b.val / 16, h57⟩ : Fin 57) = 1 from Fin.ext e, e]
      fin_cases c <;> rfl
    · rw [show (⟨b.val / 16, h57⟩ : Fin 57) = 25 from Fin.ext e, e]
      cases pub.variant <;> fin_cases c <;> rfl
    · rw [show (⟨b.val / 16, h57⟩ : Fin 57) = 30 from Fin.ext e, e]
      fin_cases c <;> rfl
    · rw [show (⟨b.val / 16, h57⟩ : Fin 57) = 27 from Fin.ext e, e]
      show (recipB pub w 0).pre c = _
      unfold recipB
      cases pub.variant <;> fin_cases c <;> rfl
    · rw [show (⟨b.val / 16, h57⟩ : Fin 57) = 28 from Fin.ext e, e]
      show (recipB pub w 1).pre c = _
      unfold recipB
      rw [hv]
      fin_cases c <;> rfl
    · rw [show (⟨b.val / 16, h57⟩ : Fin 57) = 29 from Fin.ext e, e]
      show (recipB pub w 2).pre c = _
      unfold recipB
      rw [hv]
      fin_cases c <;> rfl
  · intro b hb hn c
    have h57 : b.val / 16 < 57 := by unfold ScheduleNode at hn; omega
    have e := row_cell (cellsOf pub w) b h57 (c.castAdd 8)
    rw [buildModel]
    refine Eq.trans e ?_
    rw [hb, blockCell_pre]
    show (blocksOf pub w ⟨b.val / 16, h57⟩).pre (c.castAdd 8) = 0
    obtain ⟨l, r, hlr⟩ := blocksOf_node pub w ⟨b.val / 16, h57⟩ hn
    rw [hlr]
    exact nodeIn_pre_lo l r _ c.isLt
  · intro b hb c ha
    have h57 : b.val / 16 < 57 := by
      unfold ScheduleAbsorbs at ha; split_ifs at ha <;> omega
    rw [buildModel, row_cell _ b h57 c, hb]
    show (blocksOf pub w ⟨b.val / 16, h57⟩).absorb c = 0
    exact blocksOf_absorb_zero pub w _ c ha

#print axioms layout_block'
#print axioms state_layout
#print axioms poseidon_layout
#print axioms poseidon_model
#print axioms blockCell_pre
#print axioms blocksOf_tree_lo
#print axioms blocksOf_recip
#print axioms blocksOf_app
#print axioms blocksOf_tree_hi
#print axioms blocksOf_node
#print axioms blocksOf_hiZero
#print axioms blocksOf_absorb_zero
#print axioms schedule_model
end R0Z.BuilderModel
