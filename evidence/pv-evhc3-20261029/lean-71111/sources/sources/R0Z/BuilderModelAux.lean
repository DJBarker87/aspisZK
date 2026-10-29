import R0Z.BuilderModel
import R0P.Value
import R0P.Occupancy
import R0P.Asset

/-! Builder model, auxiliary families (t2b2b/DESIGN-BUILDER-MODEL.txt §4):
value, occupancy, asset and path hold on `layout C` from local invariants of
the aux records, and on `buildModel pub w` from named witness premises.

Premises are witness facts that the Rust builder checks before it writes the
trace (design §2): conservation (pair_trace.rs:621-628/724-729), pair-leaf
validity and spendability (pair_tree_profile.rs:124-191), the withdrawal
amount, and a non-zero change sentinel for a transfer (two_outputs,
pair_tree_profile.rs:206-226; design §5). -/
set_option autoImplicit false
noncomputable section

namespace R0Z.BuilderModel
open R0P

variable {K : Type} [Field K]

/-! ### Value -/

theorem base_poly (v : Nat) :
    valueBaseCell (K := K) v 0 + 2 * valueBaseCell v 1 + 4 * valueBaseCell v 2 +
      8 * valueBaseCell v 3 + 16 * valueBaseCell v 4 + 32 * valueBaseCell v 5 +
      64 * valueBaseCell v 6 + 128 * valueBaseCell v 7 + 256 * valueBaseCell v 8 +
      512 * valueBaseCell v 9 = ((v % 1024 : Nat) : K) :=
  (chunk10 v).symm

theorem mid_poly (v : Nat) :
    valueMidCell (K := K) v 0 + 2 * valueMidCell v 1 + 4 * valueMidCell v 2 +
      8 * valueMidCell v 3 + 16 * valueMidCell v 4 + 32 * valueMidCell v 5 +
      64 * valueMidCell v 6 + 128 * valueMidCell v 7 + 256 * valueMidCell v 8 +
      512 * valueMidCell v 9 = ((v / 1024 % 1024 : Nat) : K) :=
  (chunk10 (v / 1024)).symm

theorem hi_poly (v : Nat) :
    valueHiCell (K := K) v 0 + 2 * valueHiCell v 1 + 4 * valueHiCell v 2 +
      8 * valueHiCell v 3 + 16 * valueHiCell v 4 + 32 * valueHiCell v 5 +
      64 * valueHiCell v 6 + 128 * valueHiCell v 7 + 256 * valueHiCell v 8 +
      512 * valueHiCell v 9 = ((v / 1048576 % 1024 : Nat) : K) :=
  (chunk10 (v / 1048576)).symm

theorem value_recon (v : Nat) (hv : v < 2 ^ 30) :
    valueBaseCell (K := K) v 10 =
      ((valueBaseCell v 0 + 2 * valueBaseCell v 1 + 4 * valueBaseCell v 2 +
        8 * valueBaseCell v 3 + 16 * valueBaseCell v 4 + 32 * valueBaseCell v 5 +
        64 * valueBaseCell v 6 + 128 * valueBaseCell v 7 + 256 * valueBaseCell v 8 +
        512 * valueBaseCell v 9) +
       (valueMidCell v 0 + 2 * valueMidCell v 1 + 4 * valueMidCell v 2 +
        8 * valueMidCell v 3 + 16 * valueMidCell v 4 + 32 * valueMidCell v 5 +
        64 * valueMidCell v 6 + 128 * valueMidCell v 7 + 256 * valueMidCell v 8 +
        512 * valueMidCell v 9) * 1024) +
       (valueHiCell v 0 + 2 * valueHiCell v 1 + 4 * valueHiCell v 2 +
        8 * valueHiCell v 3 + 16 * valueHiCell v 4 + 32 * valueHiCell v 5 +
        64 * valueHiCell v 6 + 128 * valueHiCell v 7 + 256 * valueHiCell v 8 +
        512 * valueHiCell v 9) * 1048576 := by
  rw [base_poly, mid_poly, hi_poly]
  have hv' : v < 1073741824 := hv
  have hn : v = v % 1024 + v / 1024 % 1024 * 1024 + v / 1048576 % 1024 * 1048576 := by omega
  show ((v : Nat) : K) = _
  conv_lhs => rw [hn]
  push_cast
  ring

theorem value_model_range (v : Nat) (hv : v < 2 ^ 30) :
    ∀ r ∈ valueRange (⟨valueBaseCell v, valueMidCell v, valueHiCell v⟩ : Openings K), r = 0 := by
  rw [value_range_zero_iff]
  refine ⟨fun i => ?_, fun i => ?_, fun i => ?_, value_recon v hv, rfl, rfl⟩
  · show valueBaseCell v (i.castAdd 6) = 0 ∨ valueBaseCell v (i.castAdd 6) = 1
    unfold valueBaseCell
    rw [if_pos (show (i.castAdd 6).val < 10 from i.isLt)]
    exact bitK_01 _ _
  · show valueMidCell v (i.castAdd 6) = 0 ∨ valueMidCell v (i.castAdd 6) = 1
    unfold valueMidCell
    rw [if_pos (show (i.castAdd 6).val < 10 from i.isLt)]
    exact bitK_01 _ _
  · show valueHiCell v (i.castAdd 6) = 0 ∨ valueHiCell v (i.castAdd 6) = 1
    unfold valueHiCell
    rw [if_pos (show (i.castAdd 6).val < 10 from i.isLt)]
    exact bitK_01 _ _

theorem aux_1008 (C : Cells K) : auxCell C 1008 = valueBaseCell (C.values 0) := by
  funext c; simp [auxCell]
theorem aux_1009 (C : Cells K) : auxCell C 1009 = valueMidCell (C.values 0) := by
  funext c; simp [auxCell]
theorem aux_1010 (C : Cells K) : auxCell C 1010 = valueBaseCell (C.values 1) := by
  funext c; simp [auxCell]
theorem aux_1011 (C : Cells K) : auxCell C 1011 = valueMidCell (C.values 1) := by
  funext c; simp [auxCell]
theorem aux_1012 (C : Cells K) : auxCell C 1012 = valueBaseCell (C.values 2) := by
  funext c; simp [auxCell]
theorem aux_1013 (C : Cells K) : auxCell C 1013 = valueMidCell (C.values 2) := by
  funext c; simp [auxCell]
theorem aux_1016 (C : Cells K) : auxCell C 1016 = valueHiCell (C.values 2) := by
  funext c; simp [auxCell]
theorem aux_1020 (C : Cells K) : auxCell C 1020 = valueHiCell (C.values 0) := by
  funext c; simp [auxCell]
theorem aux_1022 (C : Cells K) : auxCell C 1022 = valueHiCell (C.values 1) := by
  funext c; simp [auxCell]
theorem aux_1017 (C : Cells K) : auxCell C 1017 = occCell C.inOcc := by
  funext c; simp [auxCell]
theorem aux_1018 (C : Cells K) : auxCell C 1018 = occCell C.outOcc := by
  funext c; simp [auxCell]

/-- Value family on the layout: every value below 2^30 and v0 = v1 + v2. -/
theorem value_layout (pub : Public K) (C : Cells K) (hv : ∀ j, C.values j < 2 ^ 30)
    (hcons : C.values 0 = C.values 1 + C.values 2) : Holds valueFamily pub (layout C) := by
  rw [value_holds_rows_iff]
  refine ⟨?_, ?_, ?_⟩
  · intro b hb
    rcases hb with rfl | rfl | rfl
    · rw [rowOpenings_aux C _ (by decide) (by decide) (by decide),
        show (succRow (1008 : Fin 1024)).val = 1009 from rfl,
        show (xor12Row (1008 : Fin 1024)).val = 1020 by decide,
        show (1008 : Fin 1024).val = 1008 from rfl, aux_1008, aux_1009, aux_1020]
      exact value_model_range _ (hv 0)
    · rw [rowOpenings_aux C _ (by decide) (by decide) (by decide),
        show (succRow (1010 : Fin 1024)).val = 1011 from rfl,
        show (xor12Row (1010 : Fin 1024)).val = 1022 by decide,
        show (1010 : Fin 1024).val = 1010 from rfl, aux_1010, aux_1011, aux_1022]
      exact value_model_range _ (hv 1)
    · rw [rowOpenings_aux C _ (by decide) (by decide) (by decide),
        show (succRow (1012 : Fin 1024)).val = 1013 from rfl,
        show (xor12Row (1012 : Fin 1024)).val = 1016 by decide,
        show (1012 : Fin 1024).val = 1012 from rfl, aux_1012, aux_1013, aux_1016]
      exact value_model_range _ (hv 2)
  · rw [layout_aux C 0 1014 (by decide) (by decide), layout_aux C 1 1014 (by decide) (by decide),
      layout_aux C 2 1014 (by decide) (by decide)]
    simp [auxCell]
  · rw [layout_aux C 0 1015 (by decide) (by decide), layout_aux C 1 1015 (by decide) (by decide)]
    simp only [auxCell, Fin.isValue]
    simp only [show ¬ (912 ≤ (1015 : Fin 1024).val ∧ (1015 : Fin 1024).val < 1008) by decide,
      show (1015 : Fin 1024).val = 1015 from rfl, dite_false]
    norm_num
    rw [hcons]
    push_cast
    ring

/-! ### Occupancy -/

/-- The row-local occupancy equations (PairLeaf.Valid, V7PairLeafOccupancy.lean:44). -/
def OccValid (o : OccAux K) : Prop :=
  o.occupied * (o.occupied - 1) = 0 ∧ o.commitment 7 * o.inverse - o.occupied = 0 ∧
    (1 - o.occupied) * o.inverse = 0 ∧ ∀ lane : Fin 8, (1 - o.occupied) * o.commitment lane = 0

theorem occCell_lane (o : OccAux K) (lane : Fin 8) (h : 2 + lane.val < 16) :
    occCell o ⟨2 + lane.val, h⟩ = o.commitment lane := by
  unfold occCell
  rw [if_neg (by simp), if_neg (by simp; omega), dif_pos (by simp; omega)]
  congr 1
  exact Fin.ext (by simp)

theorem occ_rows (C : Cells K) (b : Fin 1024) (o : OccAux K) (hb : auxCell C b.val = occCell o)
    (hb57 : 57 ≤ b.val / 16) (ho : OccValid o) :
    layout C 0 b * (layout C 0 b - 1) = 0 ∧
      layout C 9 b * layout C 1 b - layout C 0 b = 0 ∧
      (1 - layout C 0 b) * layout C 1 b = 0 ∧
      ∀ lane : Fin 8, (1 - layout C 0 b) * layout C ⟨2 + lane.val, by omega⟩ b = 0 := by
  have e : ∀ (c : Fin 29) (hc : c.val < 16), layout C c b = occCell o ⟨c.val, hc⟩ := by
    intro c hc
    rw [layout_aux C c b hc hb57, hb]
  rw [e 0 (by decide), e 9 (by decide), e 1 (by decide)]
  obtain ⟨h1, h2, h3, h4⟩ := ho
  refine ⟨h1, h2, h3, fun lane => ?_⟩
  rw [e _ (by simp; omega)]
  have hl := occCell_lane o lane (by omega)
  simp only at hl ⊢
  rw [hl]
  exact h4 lane

theorem occupancy_layout (pub : Public K) (C : Cells K) (hin : OccValid C.inOcc)
    (hout : OccValid C.outOcc) (hsel : C.inOcc.selected * (1 - C.inOcc.occupied) = 0)
    (hvar : C.outOcc.occupied = occupancyExpected pub.variant) :
    Holds occupancyFamily pub (layout C) := by
  rw [occupancy_holds_iff]
  refine ⟨?_, ?_, ?_⟩
  · intro b hb
    rcases hb with rfl | rfl
    · exact occ_rows C 1017 C.inOcc (aux_1017 C) (by decide) hin
    · exact occ_rows C 1018 C.outOcc (aux_1018 C) (by decide) hout
  · rw [layout_aux C 10 1017 (by decide) (by decide), layout_aux C 0 1017 (by decide) (by decide),
      show (1017 : Fin 1024).val = 1017 from rfl, aux_1017]
    exact hsel
  · rw [layout_aux C 0 1018 (by decide) (by decide), show (1018 : Fin 1024).val = 1018 from rfl,
      aux_1018]
    show C.outOcc.occupied = _
    rw [hvar]
    cases pub.variant <;> rfl

/-! ### Path -/

/-- The row-local path equations (path_holds_iff, Path.lean). -/
def PathValid (p : PathAux K) : Prop :=
  p.bit * (p.bit - 1) = 0 ∧ (∀ i : Fin 8, (1 - p.bit) * (p.left i - p.current i) = 0) ∧
    (∀ i : Fin 8, p.bit * (p.right i - p.current i) = 0)

theorem pathBaseCell_cur (p : PathAux K) (c : Fin 16) (i : Fin 8) (hc : c.val = i.val + 1) :
    pathBaseCell p c = p.current i := by
  unfold pathBaseCell
  rw [if_neg (by omega), dif_pos (by omega)]
  congr 1
  exact Fin.ext (by simp; omega)

theorem pathSuccCell_left (p : PathAux K) (c : Fin 16) (i : Fin 8) (hc : c.val = i.val) :
    pathSuccCell p c = p.left i := by
  unfold pathSuccCell
  rw [dif_pos (by omega)]
  congr 1
  exact Fin.ext (by simp; omega)

theorem pathSuccCell_right (p : PathAux K) (c : Fin 16) (i : Fin 8) (hc : c.val = 8 + i.val) :
    pathSuccCell p c = p.right i := by
  unfold pathSuccCell
  rw [dif_neg (by omega)]
  congr 1
  exact Fin.ext (by simp; omega)

theorem path_layout (pub : Public K) (C : Cells K) (hp : ∀ l, PathValid (C.path l)) :
    Holds pathFamily pub (layout C) := by
  rw [path_holds_iff]
  intro b hb
  obtain ⟨hlo, hhi, hloc⟩ := hb
  have hb1 : 912 ≤ b.val ∧ b.val < 1008 := by omega
  have hsv : (succRow b).val = b.val + 1 := by
    show (b.val + 1) % 1024 = b.val + 1
    omega
  let l : Fin 24 := ⟨4 * ((b.val - 912) / 16) + b.val % 16 / 4, by omega⟩
  have eb : ∀ (c : Fin 29) (hc : c.val < 16),
      layout C c b = pathBaseCell (C.path l) ⟨c.val, hc⟩ := by
    intro c hc
    rw [layout_aux C c b hc (by omega)]
    unfold auxCell
    rw [dif_pos hb1, if_pos (by omega)]
  have es : ∀ (c : Fin 29) (hc : c.val < 16),
      layout C c (succRow b) = pathSuccCell (C.path l) ⟨c.val, hc⟩ := by
    intro c hc
    rw [layout_aux C c (succRow b) hc (by omega), hsv]
    unfold auxCell
    rw [dif_pos (show 912 ≤ b.val + 1 ∧ b.val + 1 < 1008 by omega),
      if_neg (show ¬ ((b.val + 1) % 16 % 4 = 1) by omega),
      if_pos (show (b.val + 1) % 16 % 4 = 2 by omega)]
    exact congrArg (fun p : Fin 24 => pathSuccCell (C.path p) ⟨c.val, hc⟩)
      (Fin.ext (show 4 * ((b.val + 1 - 912) / 16) + (b.val + 1) % 16 / 4 =
        4 * ((b.val - 912) / 16) + b.val % 16 / 4 by omega))
  obtain ⟨h1, h2, h3⟩ := hp l
  have e0 : layout C 0 b = (C.path l).bit := by rw [eb 0 (by decide)]; rfl
  refine ⟨?_, fun i => ?_, fun i => ?_⟩
  · rw [e0]; exact h1
  · rw [e0, es _ (by simp; omega), eb _ (by simp; omega),
      pathSuccCell_left _ _ i (by simp), pathBaseCell_cur _ _ i (by simp)]
    exact h2 i
  · rw [e0, es _ (by simp; omega), eb _ (by simp; omega),
      pathSuccCell_right _ _ i (by simp <;> omega), pathBaseCell_cur _ _ i (by simp)]
    exact h3 i

/-! ### The model's aux records satisfy the local invariants -/

theorem pathAuxOf_valid (pub : Public K) (w : ModelWitness K) (l : Fin 24) :
    PathValid (pathAuxOf pub w l) := by
  unfold PathValid pathAuxOf
  cases (w.path l).1 <;> simp [dirK, ordered]

/-- The witness-side premises of the aux families. -/
structure AuxPremises (pub : Public K) (w : ModelWitness K) : Prop where
  conservation : w.inputValue.val = w.outputValue.val + w.changeValue.val
  pairValid : OccValid (inOccOf w)
  spendable : dirK (w.path 0).1 * (1 - w.pairOccupied) = 0
  changeSentinel : pub.variant = .privateTransfer → changeDigest pub w 7 ≠ 0
  amount : pub.variant = .withdrawal → ∀ a, pub.withdrawalAmount = some a →
    a = (w.outputValue.val : K)

theorem outOccOf_valid (pub : Public K) (w : ModelWitness K)
    (hs : pub.variant = .privateTransfer → changeDigest pub w 7 ≠ 0) :
    OccValid (outOccOf pub w) := by
  unfold OccValid outOccOf
  cases hv : pub.variant
  · have h7 := hs hv
    simp only
    refine ⟨by ring, by rw [mul_inv_cancel₀ h7]; ring, by ring, fun lane => by ring⟩
  · simp

theorem value_model (pub : Public K) (w : ModelWitness K)
    (hc : w.inputValue.val = w.outputValue.val + w.changeValue.val) :
    Holds valueFamily pub (buildModel pub w) :=
  value_layout pub _ (fun j => by
    show valuesOf w j < 2 ^ 30
    fin_cases j
    · exact w.inputValue.isLt
    · exact w.outputValue.isLt
    · exact w.changeValue.isLt) hc

theorem occupancy_model (pub : Public K) (w : ModelWitness K) (hP : AuxPremises pub w) :
    Holds occupancyFamily pub (buildModel pub w) :=
  occupancy_layout pub _ hP.pairValid (outOccOf_valid pub w hP.changeSentinel) hP.spendable
    (by show (outOccOf pub w).occupied = _
        unfold outOccOf occupancyExpected
        cases pub.variant <;> rfl)

theorem path_model (pub : Public K) (w : ModelWitness K) :
    Holds pathFamily pub (buildModel pub w) :=
  path_layout pub _ (pathAuxOf_valid pub w)

theorem asset_model (pub : Public K) (w : ModelWitness K)
    (ha : pub.variant = .withdrawal → ∀ a, pub.withdrawalAmount = some a →
      a = (w.outputValue.val : K)) :
    Holds assetFamily pub (buildModel pub w) := by
  rw [asset_holds_iff]
  refine ⟨?_, ?_, fun hv => ?_, fun hv a hwa => ?_⟩
  · rw [buildModel, layout_block _ 1 44 (by decide) 2 (by decide)]
    rfl
  · rw [buildModel, layout_block _ 1 508 (by decide) 31 (by decide)]
    rfl
  · rw [buildModel, layout_block _ 1 460 (by decide) 28 (by decide)]
    show (recipB pub w 1).absorb ⟨1, by decide⟩ = pub.assetId
    unfold recipB
    rw [hv]
    rfl
  · rw [buildModel, layout_aux _ 10 1010 (by decide) (by decide),
      show (1010 : Fin 1024).val = 1010 from rfl, aux_1010]
    rw [ha hv a hwa]
    rfl

#print axioms base_poly
#print axioms value_recon
#print axioms value_model_range
#print axioms value_layout
#print axioms occCell_lane
#print axioms occ_rows
#print axioms occupancy_layout
#print axioms pathBaseCell_cur
#print axioms pathSuccCell_left
#print axioms pathSuccCell_right
#print axioms path_layout
#print axioms pathAuxOf_valid
#print axioms outOccOf_valid
#print axioms value_model
#print axioms occupancy_model
#print axioms path_model
#print axioms asset_model
end R0Z.BuilderModel
