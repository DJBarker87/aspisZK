import R0P.CoreExt
import R0P.Zerocheck
import R0P.Schedule
import R0P.Occupancy
import Mathlib.Data.Nat.Bitwise
import R0P.Value
import R0P.Digest
import R0P.Asset
import R0P.Path
import R0P.Poseidon
import R0P.Copy
import Mathlib.Data.Fintype.BigOperators


/-! # G11: production SEM lanes at Boolean rows

Rust inspection pin: e4d68a70d3f6beb215c9f6dd418f4a2a3740c809.
T = pool_v1/pair_forest_semantic_terminal.rs,
C = pool_v1/pair_forest_copy_terminal.rs,
H = pool_v1/pair_forest_hiding.rs, under crates/aspis-statement/src.

C:143–177 expands selectors most-significant-coordinate first; H:41–46,
190–196 uses block*16+local. Thus coordinates 0–5 are block bits 5..0,
and coordinates 6–9 are local bits 3..0.

T:1143–1182 orders the 94 scalar sources: Schedule 0–31 (T:381–391),
Path 32–48, Value 49–83, Digest 84–91, Asset 92–93. Occupancy adds at
0–11 (T:529–554). T:106–124 packs consecutive four-slot groups and pads
94–95 with zero. The reversed Horner folds at T:1267–1274 put Poseidon
at theta powers 0–3, semantic groups at 4–27, and Copy at 28.

The mixed schedule/occupancy slots are separated by their disjoint row
supports. All packed semantic components lie in F by BaseTyped and the
lead's PublicBase contract. Poseidon uses its existing canonical-field
packing equivalence; its recorded raw-limb Rust refinement obligation is
unchanged. H1 (column 26) is read only by the separate Copy lane and the
helper-sum identities, not by packed semantic components.
-/

set_option autoImplicit false

namespace R0P

variable {K : Type} [Field K]

/-- Encode a Boolean vector as a natural, appending its last coordinate as
the least significant bit.  Thus the function's first coordinate is MSB. -/
def rowCode : (n : Nat) → (Fin n → Bool) → Nat
  | 0, _ => 0
  | n + 1, bits => Nat.bit (bits (Fin.last n))
      (rowCode n (fun i => bits i.castSucc))

theorem rowCode_lt (n : Nat) (bits : Fin n → Bool) : rowCode n bits < 2 ^ n := by
  induction n with
  | zero => simp [rowCode]
  | succ n ih =>
      rw [rowCode, Nat.bit_lt_two_pow_succ_iff]
      exact ih (fun i => bits i.castSucc)

/-- The bit at address `i` is the bit at binary place `n-1-i`. -/
theorem rowCode_testBit (n : Nat) (bits : Fin n → Bool) (i : Fin n) :
    (rowCode n bits).testBit (n - 1 - i.val) = bits i := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
      cases i using Fin.lastCases with
      | last =>
          have hp : n + 1 - 1 - (Fin.last n).val = 0 := by simp
          rw [hp, rowCode, Nat.testBit_bit_zero]
      | cast i =>
          have hp : n + 1 - 1 - (Fin.castSucc i).val = (n - 1 - i.val) + 1 := by
            simp only [Fin.val_castSucc]
            omega
          rw [hp, rowCode, Nat.testBit_bit_succ]
          exact ih (fun j => bits j.castSucc) i

/-- Decode a Boolean vector from the row's binary representation. -/
def rowBits (r : Fin 1024) : Fin 10 → Bool :=
  fun i => r.val.testBit (9 - i.val)

/-- Big-endian Boolean row address, matching the terminal's `block * 16 + local`
address convention. -/
def rowOf (bits : Fin 10 → Bool) : Fin 1024 :=
  ⟨rowCode 10 bits, by
    have h := rowCode_lt 10 bits
    norm_num at h ⊢
    exact h⟩

theorem rowBits_rowOf (bits : Fin 10 → Bool) : rowBits (rowOf bits) = bits := by
  funext i
  simp only [rowBits, rowOf, Fin.val_mk]
  simpa using rowCode_testBit 10 bits i

theorem rowOf_injective : Function.Injective rowOf := by
  intro b c h
  funext i
  have h' := congrFun (congrArg rowBits h) i
  simpa only [rowBits_rowOf] using h'

theorem rowOf_surjective : Function.Surjective rowOf := by
  intro r
  refine ⟨rowBits r, Fin.ext ?_⟩
  apply Nat.eq_of_testBit_eq
  intro k
  by_cases hk : k < 10
  · let i : Fin 10 := ⟨9 - k, by omega⟩
    have hb := rowCode_testBit 10 (rowBits r) i
    have hi : 10 - 1 - i.val = k := by dsimp [i]; omega
    have hi' : 9 - i.val = k := by dsimp [i]; omega
    rw [hi] at hb
    change (rowCode 10 (rowBits r)).testBit k = r.val.testBit (9 - i.val) at hb
    rw [hi'] at hb
    exact hb
  · have hpow : (2 : Nat) ^ 10 = 1024 := by norm_num
    have hr : r.val < 2 ^ 10 := by rw [hpow]; exact r.isLt
    have hc : rowCode 10 (rowBits r) < 2 ^ 10 := rowCode_lt 10 _
    have hmono : 2 ^ 10 ≤ (2 : Nat) ^ k :=
      Nat.pow_le_pow_right (by norm_num) (by omega)
    have hrk : r.val < 2 ^ k := lt_of_lt_of_le hr hmono
    have hck : rowCode 10 (rowBits r) < 2 ^ k := lt_of_lt_of_le hc hmono
    change (rowCode 10 (rowBits r)).testBit k = r.val.testBit k
    rw [Nat.testBit_eq_false_of_lt hrk, Nat.testBit_eq_false_of_lt hck]

theorem rowOf_bijective : Function.Bijective rowOf :=
  ⟨rowOf_injective, rowOf_surjective⟩

/-- Every initial schedule lane is zero when the row's low nibble is not zero.
The literal initial array has the shared `g2Low sel 0` factor, including the
two subtracting writes at lanes 8 and 9. -/
private theorem schedule_initial_zero_of_low_zero (v : Variant) (o : Openings K)
    (sel : Sel K) (hlow : g2Low sel 0 = 0) :
    ∀ j : Fin 12, scheduleInitial v o sel ⟨j.val, by omega⟩ = 0 := by
  intro j
  simp [scheduleInitial, scheduleVariantSelectors, hlow]

/-- The occupancy list is pointwise zero when both public-input selectors are
zero.  The finite split is over its twelve scalar slots only. -/
private theorem occupancy_getD_zero_of_selectors_zero (pub : Public K)
    (o : Openings K) (sel : Sel K)
    (hi : sel (63 * 16 + 9) = 0) (ho : sel (63 * 16 + 10) = 0) :
    ∀ j : Fin 12,
      (occupancyFamily.residuals pub o sel).getD j.val 0 = 0 := by
  change sel 1017 = 0 at hi
  change sel 1018 = 0 at ho
  intro j
  fin_cases j <;> simp [occupancyFamily, occupancyLanesLiteral, hi, ho]

/-- The selector rows for occupancy are distinct from every row whose low
nibble is zero. -/
private theorem occupancy_selectors_zero_of_low_nibble_zero (b : Fin 1024)
    (hmod : b.val % 16 = 0) :
    rowSel (K := K) b (63 * 16 + 9) = 0 ∧
      rowSel (K := K) b (63 * 16 + 10) = 0 := by
  have h17 : b ≠ (1017 : Fin 1024) := by
    intro h
    have hv := congrArg Fin.val h
    norm_num at hv
    omega
  have h18 : b ≠ (1018 : Fin 1024) := by
    intro h
    have hv := congrArg Fin.val h
    norm_num at hv
    omega
  constructor
  · rw [show (63 * 16 + 9 : Fin 1024) = 1017 by decide]
    exact rowSel_ne b 1017 (Ne.symm h17)
  · rw [show (63 * 16 + 10 : Fin 1024) = 1018 by decide]
    exact rowSel_ne b 1018 (Ne.symm h18)

/-- A nonzero low-zero selector can occur only on a row with low nibble zero. -/
private theorem g2_low_zero_is_zero_of_nonnibble_zero (b : Fin 1024)
    (hmod : b.val % 16 ≠ 0) : g2Low (rowSel (K := K) b) 0 = 0 := by
  rw [g2_low_row]
  have hne : ¬ (0 : Nat) = b.val % 16 := by simpa [eq_comm] using hmod
  simp only [Fin.val_zero]
  simp [hne]

/-- On Boolean rows, the combined schedule/occupancy scalar summand vanishes
everywhere iff each of its two disjointly supported summands vanishes.  The
occupancy list uses its literal `getD 0` default convention. -/
theorem schedule_occupancy_separate (pub : Public K) (A : Trace K) :
    (∀ b : Fin 1024, ∀ j : Fin 12,
      scheduleInitial pub.variant (rowOpenings A b) (rowSel b)
          ⟨j.val, by omega⟩ +
        (occupancyFamily.residuals pub (rowOpenings A b) (rowSel b)).getD j.val 0 = 0) ↔
    (∀ b : Fin 1024, ∀ j : Fin 12,
      scheduleInitial pub.variant (rowOpenings A b) (rowSel b)
          ⟨j.val, by omega⟩ = 0) ∧
    (∀ b : Fin 1024, ∀ j : Fin 12,
      (occupancyFamily.residuals pub (rowOpenings A b) (rowSel b)).getD j.val 0 = 0) := by
  constructor
  · intro h
    constructor
    · intro b j
      by_cases hmod : b.val % 16 = 0
      · obtain ⟨hi, ho⟩ := occupancy_selectors_zero_of_low_nibble_zero (K := K) b hmod
        have hocc := occupancy_getD_zero_of_selectors_zero pub (rowOpenings A b)
          (rowSel b) hi ho j
        simpa only [hocc, add_zero] using h b j
      · have hlow := g2_low_zero_is_zero_of_nonnibble_zero (K := K) b hmod
        have hsched := schedule_initial_zero_of_low_zero pub.variant (rowOpenings A b)
          (rowSel b) hlow j
        exact hsched
    · intro b j
      by_cases hmod : b.val % 16 = 0
      · obtain ⟨hi, ho⟩ := occupancy_selectors_zero_of_low_nibble_zero (K := K) b hmod
        exact occupancy_getD_zero_of_selectors_zero pub (rowOpenings A b)
          (rowSel b) hi ho j
      · have hlow := g2_low_zero_is_zero_of_nonnibble_zero (K := K) b hmod
        have hsched := schedule_initial_zero_of_low_zero pub.variant (rowOpenings A b)
          (rowSel b) hlow j
        simpa only [hsched, zero_add] using h b j
  · rintro ⟨hs, ho⟩ b j
    rw [hs b j, ho b j, zero_add]

#print axioms rowCode
#print axioms rowCode_lt
#print axioms rowCode_testBit
#print axioms rowBits
#print axioms rowOf
#print axioms rowBits_rowOf
#print axioms rowOf_injective
#print axioms rowOf_surjective
#print axioms rowOf_bijective
#print axioms schedule_initial_zero_of_low_zero
#print axioms occupancy_getD_zero_of_selectors_zero
#print axioms occupancy_selectors_zero_of_low_nibble_zero
#print axioms g2_low_zero_is_zero_of_nonnibble_zero
#print axioms schedule_occupancy_separate


private theorem lane_rowSel_mem (F : Subfield K) (b k : Fin 1024) :
    rowSel (K := K) b k ∈ F := by
  unfold rowSel
  split_ifs
  · exact F.one_mem
  · exact F.zero_mem

#print axioms lane_rowSel_mem

private theorem lane_openings_mem (F : Subfield K) (t : Trace K)
    (hA : BaseTyped F t) (b : Fin 1024) :
    (∀ c, (rowOpenings t b).z c ∈ F) ∧
    (∀ c, (rowOpenings t b).succ c ∈ F) ∧
    (∀ c, (rowOpenings t b).xor12 c ∈ F) := by
  constructor
  · intro c
    exact hA (c.castAdd 13) (by change c.val < 26; have := c.isLt; omega) b
  constructor
  · intro c
    exact hA (c.castAdd 13) (by change c.val < 26; have := c.isLt; omega) (succRow b)
  · intro c
    exact hA (c.castAdd 13) (by change c.val < 26; have := c.isLt; omega) (xor12Row b)

#print axioms lane_openings_mem

private theorem lane_schedule_target_mem (F : Subfield K) (v : Variant)
    (block : Nat) (c : Fin 16) : scheduleTarget (K := K) v block c ∈ F := by
  unfold scheduleTarget
  split_ifs
  all_goals first | exact F.zero_mem | exact natCast_mem F _

#print axioms lane_schedule_target_mem

theorem lane_schedule_mem (F : Subfield K) (pub : Public K) (t : Trace K)
    (hA : BaseTyped F t) (_hpub : PublicBase F pub) (b : Fin 1024) :
    ∀ r ∈ scheduleFamily.residuals pub (rowOpenings t b) (rowSel b), r ∈ F := by
  simp only [scheduleFamily, List.forall_mem_append, List.forall_mem_ofFn_iff]
  have ht (c : Fin 16) : t (c.castAdd 13) b ∈ F :=
    hA (c.castAdd 13) (by change c.val < 26; have := c.isLt; omega) b
  constructor
  · intro c
    rw [schedule_initial_row]
    split_ifs
    all_goals first
      | exact F.sub_mem (ht c) (lane_schedule_target_mem F _ _ c)
      | exact ht c
      | exact F.zero_mem
  · intro c
    rw [schedule_absorption_row]
    split_ifs
    · exact ht c
    · exact F.zero_mem

#print axioms lane_schedule_mem

theorem lane_path_mem (F : Subfield K) (pub : Public K) (t : Trace K)
    (hA : BaseTyped F t) (_hpub : PublicBase F pub) (b : Fin 1024) :
    ∀ r ∈ pathFamily.residuals pub (rowOpenings t b) (rowSel b), r ∈ F := by
  obtain ⟨hz, hs, _⟩ := lane_openings_mem F t hA b
  have hq : pathSelector (rowSel (K := K) b) ∈ F := by
    rw [path_selector_row]
    split_ifs
    · exact F.one_mem
    · exact F.zero_mem
  simp only [pathFamily, pathLanes, List.forall_mem_append, List.forall_mem_cons,
    List.not_mem_nil, false_implies, implies_true, and_true, List.forall_mem_ofFn_iff]
  repeat' first
    | constructor
    | intro i
    | exact hq
    | apply F.mul_mem
    | apply F.sub_mem
    | exact hz _
    | exact hs _
    | exact F.one_mem

#print axioms lane_path_mem

private theorem lane_reconstruct_mem (F : Subfield K) (view : Fin 16 → K)
    (hv : ∀ i, view i ∈ F) : valueReconstruct10 view ∈ F := by
  rw [value_reconstruct10_eq]
  repeat' first
    | apply F.add_mem
    | apply F.mul_mem
    | exact hv _
    | exact natCast_mem F _

#print axioms lane_reconstruct_mem

private theorem lane_value_range_mem (F : Subfield K) (o : Openings K)
    (hz : ∀ i, o.z i ∈ F) (hs : ∀ i, o.succ i ∈ F)
    (hx : ∀ i, o.xor12 i ∈ F) : ∀ r ∈ valueRange o, r ∈ F := by
  have hrz := lane_reconstruct_mem F o.z hz
  have hrs := lane_reconstruct_mem F o.succ hs
  have hrx := lane_reconstruct_mem F o.xor12 hx
  simp only [valueRange, List.forall_mem_append, List.forall_mem_ofFn_iff,
    List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true, and_true]
  repeat' first
    | constructor
    | intro i
    | exact hrz
    | exact hrs
    | exact hrx
    | apply F.add_mem
    | apply F.sub_mem
    | apply F.mul_mem
    | apply F.pow_mem
    | exact hz _
    | exact hs _
    | exact hx _
    | exact natCast_mem F _

#print axioms lane_value_range_mem

theorem lane_value_mem (F : Subfield K) (pub : Public K) (t : Trace K)
    (hA : BaseTyped F t) (_hpub : PublicBase F pub) (b : Fin 1024) :
    ∀ r ∈ valueFamily.residuals pub (rowOpenings t b) (rowSel b), r ∈ F := by
  obtain ⟨hz, hs, hx⟩ := lane_openings_mem F t hA b
  change ∀ r ∈ (valueRange (rowOpenings t b)).map
    (fun r => (((0 + rowSel b 1008) + rowSel b 1010) + rowSel b 1012) * r) ++
    [rowSel b 1014 * (((rowOpenings t b).z 0-(rowOpenings t b).z 1)-
      (rowOpenings t b).z 2),
     rowSel b 1014 * ((rowOpenings t b).succ 0-(rowOpenings t b).succ 1)], r ∈ F
  simp only [List.forall_mem_append, List.forall_mem_map, List.forall_mem_cons,
    List.not_mem_nil, false_implies, implies_true, and_true]
  constructor
  · intro r hr
    apply F.mul_mem
    · repeat' first | apply F.add_mem | exact lane_rowSel_mem F b _ | exact F.zero_mem
    · exact lane_value_range_mem F _ hz hs hx r hr
  · repeat' first
      | constructor
      | apply F.mul_mem
      | apply F.sub_mem
      | exact lane_rowSel_mem F b _
      | exact hz _
      | exact hs _

#print axioms lane_value_mem

theorem lane_occupancy_mem (F : Subfield K) (pub : Public K) (t : Trace K)
    (hA : BaseTyped F t) (_hpub : PublicBase F pub) (b : Fin 1024) :
    ∀ r ∈ occupancyFamily.residuals pub (rowOpenings t b) (rowSel b), r ∈ F := by
  have hz := (lane_openings_mem F t hA b).1
  have he : occupancyExpected (K := K) pub.variant ∈ F := by
    cases pub.variant
    · exact F.one_mem
    · exact F.zero_mem
  simp only [occupancyFamily, occupancyLanesLiteral, List.forall_mem_append,
    List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true,
    and_true, List.forall_mem_ofFn_iff]
  repeat' first
    | constructor
    | intro i
    | exact he
    | apply F.add_mem
    | apply F.sub_mem
    | apply F.mul_mem
    | exact hz _
    | exact lane_rowSel_mem F b _
    | exact F.one_mem

#print axioms lane_occupancy_mem

private theorem lane_empty_root_target_mem (F : Subfield K)
    (level : Fin 20) (i : Fin 8) : emptyRootRightTarget (K := K) level i ∈ F := by
  unfold emptyRootRightTarget
  split_ifs <;> exact natCast_mem F _

#print axioms lane_empty_root_target_mem

private theorem lane_digest_target_mem (F : Subfield K) (pub : Public K)
    (hpub : PublicBase F pub) (key : DigestKey) (i : Fin 8) :
    digestTarget pub key i ∈ F := by
  obtain ⟨ha, hn, _, hr, hc, _, hs, hroot, hnext⟩ := hpub
  cases key with
  | anchor => exact ha i
  | nullifier => exact hn i
  | recipient =>
      cases he : pub.recipient with
      | none => simp only [digestTarget, he, Option.getD_none]; exact F.zero_mem
      | some r =>
          simp only [digestTarget, he, Option.getD_some]
          exact hr r he i
  | change => exact hc i
  | frontier level =>
      simp only [digestTarget]
      split_ifs
      · exact lane_empty_root_target_mem F level i
      · exact hs level i
  | nextRoot => exact hroot i
  | carry =>
      simp only [digestTarget]
      split_ifs
      · exact hnext _ i
      · exact F.zero_mem

#print axioms lane_digest_target_mem

theorem lane_digest_mem (F : Subfield K) (pub : Public K) (t : Trace K)
    (hA : BaseTyped F t) (hpub : PublicBase F pub) (b : Fin 1024) :
    ∀ r ∈ digestFamily.residuals pub (rowOpenings t b) (rowSel b), r ∈ F := by
  have hz := (lane_openings_mem F t hA b).1
  simp only [digestFamily, List.forall_mem_ofFn_iff]
  intro i
  unfold publicDigestLanes
  rw [digest_fold_eq]
  apply F.add_mem F.zero_mem
  apply F.list_sum_mem
  intro x hx
  obtain ⟨key, _, rfl⟩ := List.mem_map.mp hx
  exact F.mul_mem (lane_rowSel_mem F b _)
    (F.sub_mem (hz _) (lane_digest_target_mem F pub hpub key i))

#print axioms lane_digest_mem

theorem lane_asset_mem (F : Subfield K) (pub : Public K) (t : Trace K)
    (hA : BaseTyped F t) (hpub : PublicBase F pub) (b : Fin 1024) :
    ∀ r ∈ assetFamily.residuals pub (rowOpenings t b) (rowSel b), r ∈ F := by
  have hz := (lane_openings_mem F t hA b).1
  have hasset : pub.assetId ∈ F := hpub.2.2.1
  have hamount : pub.withdrawalAmount.getD 0 ∈ F := by
    cases he : pub.withdrawalAmount with
    | none => simp only [Option.getD_none]; exact F.zero_mem
    | some a =>
        simp only [Option.getD_some]
        exact hpub.2.2.2.2.2.1 a he
  cases hv : pub.variant <;> cases hw : pub.withdrawalAmount.isSome
  all_goals
    simp only [assetFamily, assetScalarLanes, hv, hw, Bool.false_eq_true,
      ite_false, ite_true, List.forall_mem_cons, List.not_mem_nil,
      false_implies, implies_true, and_true]
    repeat' first
      | constructor
      | apply F.add_mem
      | apply F.sub_mem
      | apply F.mul_mem
      | exact hz _
      | exact hasset
      | exact hamount
      | exact lane_rowSel_mem F b _

#print axioms lane_asset_mem

open Sumcheck

/-- T:1143–1182, source scalar slots 0–93 at a Boolean row, with the occupancy addition
at slots 0–11 and source-order defaults at every family boundary. -/
def scalarLaneRow (pub : Public K) (t : Trace K) (b : Fin 1024) (i : Nat) : K :=
  let o := rowOpenings t b
  let sel := rowSel b
  if i < 12 then
    (scheduleFamily.residuals pub o sel).getD i 0 +
      (occupancyFamily.residuals pub o sel).getD i 0
  else if i < 32 then (scheduleFamily.residuals pub o sel).getD i 0
  else if i < 49 then (pathFamily.residuals pub o sel).getD (i - 32) 0
  else if i < 84 then (valueFamily.residuals pub o sel).getD (i - 49) 0
  else if i < 92 then (digestFamily.residuals pub o sel).getD (i - 84) 0
  else if i < 94 then (assetFamily.residuals pub o sel).getD (i - 92) 0
  else 0

#print axioms scalarLaneRow

/-- Fixed 94-slot source lane map, indexed by a Boolean row address. -/
def scalarLane (t : Trace K) (pub : Public K) : Fin 94 → (Fin 10 → Bool) → K :=
  fun i bits => scalarLaneRow pub t (rowOf bits) i.val

#print axioms scalarLane

/-- T:106–124, one packed semantic source group in four-component order;
slots 94–95 are the two explicit zero-padding components. -/
def semanticPackedLane {F : Subfield K} (B : PackBasis F)
    (pub : Public K) (t : Trace K) (b : Fin 1024) (group : Fin 24) : K :=
  pack4 B (fun j => scalarLaneRow pub t b (4 * group.val + j.val))

#print axioms semanticPackedLane

/-- T:1267–1274, production theta lanes: Poseidon packed groups 0–3, semantic packed
source groups 0–23, then the explicit-input Copy residual. -/
def laneOf (t : Trace K) (pub : Public K) (lam chi : K)
    {F : Subfield K} (B : PackBasis F) : Fin 29 → (Fin 10 → Bool) → K :=
  fun i bits =>
    let b := rowOf bits
    if h : i.val < 4 then
      ((poseidonPackedFamily B).residuals pub (rowOpenings t b) (rowSel b)).getD i.val 0
    else if h : i.val < 28 then
      semanticPackedLane B pub t b ⟨i.val - 4, by omega⟩
    else
      (copyFamily.residuals pub lam chi (rowOpenings t b) (t 26 b) (rowSel b)).getD 0 0

#print axioms laneOf

private theorem list_getD_zero_iff {α : Type} [Zero α]
    (xs : List α) :
    (∀ i, i < xs.length → xs.getD i 0 = 0) ↔ ∀ x ∈ xs, x = 0 := by
  constructor
  · intro h x hx
    obtain ⟨i, hi, hxi⟩ := List.mem_iff_getElem.mp hx
    have hval := h i hi
    rw [List.getD_eq_getElem _ _ hi] at hval
    simpa [hxi] using hval
  · intro h i hi
    rw [List.getD_eq_getElem _ _ hi]
    exact h _ (List.mem_iff_getElem.mpr ⟨i, hi, rfl⟩)

#print axioms list_getD_zero_iff

private theorem rowOf_rowBits (r : Fin 1024) : rowOf (rowBits r) = r := by
  obtain ⟨bits, hb⟩ := rowOf_surjective r
  have hbits : rowBits r = bits := by
    rw [← hb]
    exact rowBits_rowOf bits
  rw [hbits]
  exact hb

#print axioms rowOf_rowBits

private theorem getD_mem_of_lt {α : Type} (xs : List α) (i : Nat) (d : α)
    (hi : i < xs.length) : xs.getD i d ∈ xs := by
  rw [List.getD_eq_getElem _ _ hi]
  exact List.mem_iff_getElem.mpr ⟨i, hi, rfl⟩

#print axioms getD_mem_of_lt

private theorem getD_ofFn_eq {α : Type} {n : Nat} (f : Fin n → α)
    (i : Nat) (d : α) (hi : i < n) :
    (List.ofFn f).getD i d = f ⟨i, hi⟩ := by
  have hlen : i < (List.ofFn f).length := by simpa using hi
  rw [List.getD_eq_getElem _ _ hlen]
  simp only [List.getElem_ofFn]

#print axioms getD_ofFn_eq

private theorem scalarLaneRow_mem (F : Subfield K) (_B : PackBasis F)
    (pub : Public K) (t : Trace K) (hA : BaseTyped F t) (hpub : PublicBase F pub)
    (b : Fin 1024) (i : Nat) (hi : i < 94) : scalarLaneRow pub t b i ∈ F := by
  by_cases h12 : i < 12
  · simp only [scalarLaneRow, if_pos h12]
    apply F.add_mem
    · exact lane_schedule_mem F pub t hA hpub b _
        (getD_mem_of_lt _ _ _ (by
          have hlen : i < 32 := by omega
          simpa only [scheduleFamily, List.length_append, List.length_ofFn] using hlen))
    · exact lane_occupancy_mem F pub t hA hpub b _
        (getD_mem_of_lt _ _ _ (by
          have hlen : i < 12 := h12
          simpa only [occupancyFamily, occupancyLanesLiteral, List.length_append, List.length_cons, List.length_nil, List.length_ofFn] using hlen))
  · by_cases h32 : i < 32
    · simp only [scalarLaneRow, if_neg h12, if_pos h32]
      exact lane_schedule_mem F pub t hA hpub b _
        (getD_mem_of_lt _ _ _ (by
          simpa only [scheduleFamily, List.length_append, List.length_ofFn] using h32))
    · by_cases h49 : i < 49
      · simp only [scalarLaneRow, if_neg h12, if_neg h32, if_pos h49]
        exact lane_path_mem F pub t hA hpub b _
          (getD_mem_of_lt _ _ _ (by simp [pathFamily, pathLanes]; omega))
      · by_cases h84 : i < 84
        · simp only [scalarLaneRow, if_neg h12, if_neg h32, if_neg h49, if_pos h84]
          exact lane_value_mem F pub t hA hpub b _
            (getD_mem_of_lt _ _ _ (by simp [valueFamily, valueRange]; omega))
        · by_cases h92 : i < 92
          · simp only [scalarLaneRow, if_neg h12, if_neg h32, if_neg h49,
              if_neg h84, if_pos h92]
            exact lane_digest_mem F pub t hA hpub b _
              (getD_mem_of_lt _ _ _ (by simp only [digestFamily, List.length_ofFn]; omega))
          · by_cases h94 : i < 94
            · simp only [scalarLaneRow, if_neg h12, if_neg h32, if_neg h49,
                if_neg h84, if_neg h92, if_pos h94]
              exact lane_asset_mem F pub t hA hpub b _
                (getD_mem_of_lt _ _ _ (by simp only [assetFamily, assetScalarLanes, List.length_cons, List.length_nil]; omega))
            · omega

#print axioms scalarLaneRow_mem

private theorem semanticPackedLane_mem (F : Subfield K) (_B : PackBasis F)
    (pub : Public K) (t : Trace K) (hA : BaseTyped F t) (hpub : PublicBase F pub)
    (b : Fin 1024) (g : Fin 24) (j : Fin 4) :
    scalarLaneRow pub t b (4 * g.val + j.val) ∈ F := by
  by_cases hi : 4 * g.val + j.val < 94
  · exact scalarLaneRow_mem F _B pub t hA hpub b _ hi
  · have hz : scalarLaneRow pub t b (4 * g.val + j.val) = 0 := by
      have h12 : ¬ 4 * g.val + j.val < 12 := by omega
      have h32 : ¬ 4 * g.val + j.val < 32 := by omega
      have h49 : ¬ 4 * g.val + j.val < 49 := by omega
      have h84 : ¬ 4 * g.val + j.val < 84 := by omega
      have h92 : ¬ 4 * g.val + j.val < 92 := by omega
      simp only [scalarLaneRow, if_neg h12, if_neg h32, if_neg h49,
        if_neg h84, if_neg h92, if_neg hi]
    rw [hz]
    exact F.zero_mem

#print axioms semanticPackedLane_mem

/-- The per-row scalar source contributions vanish exactly when their source
families do, after separating the schedule/occupancy support at slots 0–11. -/
private theorem scalarRows_zero_iff (pub : Public K) (t : Trace K) :
    (∀ b i, i < 94 → scalarLaneRow pub t b i = 0) ↔
      (Holds valueFamily pub t ∧ Holds occupancyFamily pub t ∧
       Holds assetFamily pub t ∧ Holds scheduleFamily pub t ∧
       Holds pathFamily pub t ∧ Holds digestFamily pub t) := by
  constructor
  · intro h
    have hsep :
        (∀ b : Fin 1024, ∀ j : Fin 12,
          scheduleInitial pub.variant (rowOpenings t b) (rowSel b) ⟨j.val, by omega⟩ +
            (occupancyFamily.residuals pub (rowOpenings t b) (rowSel b)).getD j.val 0 = 0) := by
      intro b j
      have hj94 : j.val < 94 := by have hj := j.isLt; omega
      have hslot := h b j.val hj94
      have hsched :
          (scheduleFamily.residuals pub (rowOpenings t b) (rowSel b)).getD j.val 0 =
            scheduleInitial pub.variant (rowOpenings t b) (rowSel b) ⟨j.val, by omega⟩ := by
        change (List.ofFn (scheduleInitial pub.variant (rowOpenings t b) (rowSel b)) ++
          List.ofFn (scheduleAbsorption pub.variant (rowOpenings t b) (rowSel b))).getD j.val 0 = _
        rw [List.getD_append _ _ _ _ (by simp only [List.length_ofFn]; omega)]
        exact getD_ofFn_eq _ _ _ (lt_of_lt_of_le j.isLt (by decide))
      simp only [scalarLaneRow, if_pos (show j.val < 12 by omega)] at hslot
      rw [hsched] at hslot
      exact hslot
    have hsep' := (schedule_occupancy_separate pub t).mp hsep
    have hOcc : Holds occupancyFamily pub t := by
      intro b r hr
      have hD : ∀ i, i < (occupancyFamily.residuals pub (rowOpenings t b) (rowSel b)).length →
          (occupancyFamily.residuals pub (rowOpenings t b) (rowSel b)).getD i 0 = 0 := by
        intro i hi
        have hi12 : i < 12 := by simpa [occupancyFamily, occupancyLanesLiteral] using hi
        exact hsep'.2 b ⟨i, hi12⟩
      exact (list_getD_zero_iff _).mp hD r hr
    have hSchedule : Holds scheduleFamily pub t := by
      intro b r hr
      rw [scheduleFamily, List.mem_append] at hr
      rcases hr with hi | ha
      · obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hi
        have hsched :
            (scheduleFamily.residuals pub (rowOpenings t b) (rowSel b)).getD j.val 0 =
              scheduleInitial pub.variant (rowOpenings t b) (rowSel b) j := by
          change (List.ofFn (scheduleInitial pub.variant (rowOpenings t b) (rowSel b)) ++
            List.ofFn (scheduleAbsorption pub.variant (rowOpenings t b) (rowSel b))).getD j.val 0 = _
          rw [List.getD_append _ _ _ _ (by simp only [List.length_ofFn]; omega)]
          exact getD_ofFn_eq _ _ _ j.isLt
        by_cases hj : j.val < 12
        · exact hsep'.1 b ⟨j.val, hj⟩
        · have hs := h b j.val (by omega)
          have h32 : j.val < 32 := by omega
          simp only [scalarLaneRow, if_neg (by omega), if_pos h32] at hs
          rw [hsched] at hs
          exact hs
      · obtain ⟨j, rfl⟩ := List.mem_ofFn.mp ha
        have habs :
            (scheduleFamily.residuals pub (rowOpenings t b) (rowSel b)).getD (16 + j.val) 0 =
              scheduleAbsorption pub.variant (rowOpenings t b) (rowSel b) j := by
          change (List.ofFn (scheduleInitial pub.variant (rowOpenings t b) (rowSel b)) ++
            List.ofFn (scheduleAbsorption pub.variant (rowOpenings t b) (rowSel b))).getD (16 + j.val) 0 = _
          rw [List.getD_append_right _ _ _ _ (by simp)]
          have hfirst :
              (List.ofFn (scheduleInitial pub.variant (rowOpenings t b) (rowSel b))).length = 16 := by
            simp
          rw [hfirst]
          have hsub : 16 + j.val - 16 = j.val := by omega
          rw [hsub]
          exact getD_ofFn_eq _ _ _ j.isLt
        have hs := h b (16 + j.val) (by have hj := j.isLt; omega)
        have h12 : ¬ 16 + j.val < 12 := by omega
        have h32 : 16 + j.val < 32 := by omega
        simp only [scalarLaneRow, if_neg h12, if_pos h32] at hs
        rw [habs] at hs
        exact hs
    have hPath : Holds pathFamily pub t := by
      intro b r hr
      have hD : ∀ i, i < (pathFamily.residuals pub (rowOpenings t b) (rowSel b)).length →
          (pathFamily.residuals pub (rowOpenings t b) (rowSel b)).getD i 0 = 0 := by
        intro i hi
        have hi17 : i < 17 := by simpa [pathFamily, pathLanes] using hi
        have hs := h b (32 + i) (by omega)
        have h12 : ¬ 32 + i < 12 := by omega
        have h32 : ¬ 32 + i < 32 := by omega
        have h49 : 32 + i < 49 := by omega
        simp only [scalarLaneRow, if_neg h12, if_neg h32, if_pos h49,
          Nat.add_sub_cancel_left] at hs
        exact hs
      exact (list_getD_zero_iff _).mp hD r hr
    have hValue : Holds valueFamily pub t := by
      intro b r hr
      have hD : ∀ i, i < (valueFamily.residuals pub (rowOpenings t b) (rowSel b)).length →
          (valueFamily.residuals pub (rowOpenings t b) (rowSel b)).getD i 0 = 0 := by
        intro i hi
        have hvlen : (valueFamily.residuals pub (rowOpenings t b) (rowSel b)).length = 35 := by
          simp [valueFamily, valueRange]
        have hi35 : i < 35 := by simpa only [hvlen] using hi
        have hs := h b (49 + i) (by omega)
        have h12 : ¬ 49 + i < 12 := by omega
        have h32 : ¬ 49 + i < 32 := by omega
        have h49 : ¬ 49 + i < 49 := by omega
        have h84 : 49 + i < 84 := by omega
        simp only [scalarLaneRow, if_neg h12, if_neg h32, if_neg h49, if_pos h84,
          Nat.add_sub_cancel_left] at hs
        exact hs
      exact (list_getD_zero_iff _).mp hD r hr
    have hDigest : Holds digestFamily pub t := by
      intro b r hr
      have hD : ∀ i, i < (digestFamily.residuals pub (rowOpenings t b) (rowSel b)).length →
          (digestFamily.residuals pub (rowOpenings t b) (rowSel b)).getD i 0 = 0 := by
        intro i hi
        have hi8 : i < 8 := by simpa [digestFamily] using hi
        have hs := h b (84 + i) (by omega)
        have h12 : ¬ 84 + i < 12 := by omega
        have h32 : ¬ 84 + i < 32 := by omega
        have h49 : ¬ 84 + i < 49 := by omega
        have h84 : ¬ 84 + i < 84 := by omega
        have h92 : 84 + i < 92 := by omega
        simp only [scalarLaneRow, if_neg h12, if_neg h32, if_neg h49, if_neg h84,
          if_pos h92, Nat.add_sub_cancel_left] at hs
        exact hs
      exact (list_getD_zero_iff _).mp hD r hr
    have hAsset : Holds assetFamily pub t := by
      intro b r hr
      have hD : ∀ i, i < (assetFamily.residuals pub (rowOpenings t b) (rowSel b)).length →
          (assetFamily.residuals pub (rowOpenings t b) (rowSel b)).getD i 0 = 0 := by
        intro i hi
        have hi2 : i < 2 := by simpa [assetFamily, assetScalarLanes] using hi
        have hs := h b (92 + i) (by omega)
        have h12 : ¬ 92 + i < 12 := by omega
        have h32 : ¬ 92 + i < 32 := by omega
        have h49 : ¬ 92 + i < 49 := by omega
        have h84 : ¬ 92 + i < 84 := by omega
        have h92 : ¬ 92 + i < 92 := by omega
        have h94 : 92 + i < 94 := by omega
        simp only [scalarLaneRow, if_neg h12, if_neg h32, if_neg h49, if_neg h84,
          if_neg h92, if_pos h94, Nat.add_sub_cancel_left] at hs
        exact hs
      exact (list_getD_zero_iff _).mp hD r hr
    exact ⟨hValue, hOcc, hAsset, hSchedule, hPath, hDigest⟩
  · rintro ⟨hValue, hOcc, hAsset, hSchedule, hPath, hDigest⟩ b i hi
    by_cases h12 : i < 12
    · have hs := hSchedule b
      have ho := hOcc b
      have hs0 : (scheduleFamily.residuals pub (rowOpenings t b) (rowSel b)).getD i 0 = 0 := by
        have hD := (list_getD_zero_iff _).mpr hs
        exact hD i (by simp only [scheduleFamily, List.length_append,
          List.length_ofFn]; omega)
      have ho0 : (occupancyFamily.residuals pub (rowOpenings t b) (rowSel b)).getD i 0 = 0 := by
        have hD := (list_getD_zero_iff _).mpr ho
        exact hD i (by simp [occupancyFamily, occupancyLanesLiteral]; omega)
      simp only [scalarLaneRow, if_pos h12, hs0, ho0, zero_add]
    · by_cases h32 : i < 32
      · have hs := hSchedule b
        have hD := (list_getD_zero_iff _).mpr hs
        have hlen : i < (scheduleFamily.residuals pub (rowOpenings t b) (rowSel b)).length :=
          by simpa only [scheduleFamily, List.length_append, List.length_ofFn] using
            (show i < 32 by omega)
        have hz := hD i hlen
        have h32' : i < 32 := by omega
        simpa only [scalarLaneRow, if_neg h12, if_pos h32'] using hz
      · by_cases h49 : i < 49
        · have hp := hPath b
          have hD := (list_getD_zero_iff _).mpr hp
          have hlen : i - 32 < (pathFamily.residuals pub (rowOpenings t b) (rowSel b)).length := by
            simpa [pathFamily, pathLanes] using (show i - 32 < 17 by omega)
          have hz := hD (i - 32) hlen
          simpa only [scalarLaneRow, if_neg h12, if_neg h32, if_pos h49] using hz
        · by_cases h84 : i < 84
          · have hv := hValue b
            have hD := (list_getD_zero_iff _).mpr hv
            have hlen : i - 49 < (valueFamily.residuals pub (rowOpenings t b) (rowSel b)).length := by
              simpa [valueFamily, valueRange] using (show i - 49 < 35 by omega)
            have hz := hD (i - 49) hlen
            simpa only [scalarLaneRow, if_neg h12, if_neg h32, if_neg h49, if_pos h84] using hz
          · by_cases h92 : i < 92
            · have hd := hDigest b
              have hD := (list_getD_zero_iff _).mpr hd
              have hlen : i - 84 < (digestFamily.residuals pub (rowOpenings t b) (rowSel b)).length := by
                simpa only [digestFamily, List.length_ofFn] using (show i - 84 < 8 by omega)
              have hz := hD (i - 84) hlen
              simpa only [scalarLaneRow, if_neg h12, if_neg h32, if_neg h49,
                if_neg h84, if_pos h92] using hz
            · have ha := hAsset b
              have hD := (list_getD_zero_iff _).mpr ha
              have hlt : i - 92 < (assetFamily.residuals pub (rowOpenings t b) (rowSel b)).length := by
                simpa [assetFamily, assetScalarLanes] using (show i - 92 < 2 by omega)
              have hz := hD (i - 92) hlt
              simpa only [scalarLaneRow, if_neg h12, if_neg h32, if_neg h49,
                if_neg h84, if_neg h92, if_pos hi] using hz

#print axioms scalarRows_zero_iff

theorem lanes_zero_iff_holds (F : Subfield K) (B : PackBasis F)
    (pub : Public K) (lam chi : K) (t : Trace K)
    (hA : BaseTyped F t) (hpub : PublicBase F pub) :
    (∀ i b, laneOf t pub lam chi B i b = 0) ↔
      (Holds valueFamily pub t ∧ Holds occupancyFamily pub t ∧
       Holds assetFamily pub t ∧ Holds scheduleFamily pub t ∧
       Holds pathFamily pub t ∧ Holds digestFamily pub t ∧
       Holds poseidonScalarFamily pub t ∧ CHolds copyFamily pub lam chi t) := by
  constructor
  · intro hzero
    have hrow (i : Fin 29) (r : Fin 1024) : laneOf t pub lam chi B i (rowBits r) = 0 :=
      hzero i (rowBits r)
    have hscalar : ∀ r i, i < 94 → scalarLaneRow pub t r i = 0 := by
      intro r i hi
      let g : Fin 24 := ⟨i / 4, by omega⟩
      let j : Fin 4 := ⟨i % 4, Nat.mod_lt _ (by omega)⟩
      have hg := hrow ⟨4 + g.val, by omega⟩ r
      have hg4 : 4 + g.val < 28 := by omega
      have hpack : semanticPackedLane B pub t r g = 0 := by
        simpa [laneOf, rowOf_rowBits r, hg4] using hg
      have hzero4 := (pack4_eq_zero_iff B _ (fun q => semanticPackedLane_mem F B pub t hA hpub r g q)).mp hpack
      have hindex : 4 * g.val + j.val = i := by dsimp [g, j]; omega
      simpa [hindex, j] using hzero4 j
    have hsem := (scalarRows_zero_iff pub t).mp hscalar
    have hposePacked : Holds (poseidonPackedFamily B) pub t := by
      intro r x hx
      obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hx
      have hz := hrow ⟨j.val, by omega⟩ r
      have hget :
          ((poseidonPackedFamily B).residuals pub (rowOpenings t r) (rowSel r)).getD j.val 0 =
            pack4 B (fun limb => poseidonScalarResidual (rowOpenings t r)
              (g2SumHigh (rowSel r) 0 57 (by omega)) (g2Low (rowSel r))
              ⟨4 * j.val + limb.val, by omega⟩) := by
        change (List.ofFn (fun group : Fin 4 => pack4 B (fun limb =>
          poseidonScalarResidual (rowOpenings t r) (g2SumHigh (rowSel r) 0 57 (by omega))
            (g2Low (rowSel r)) ⟨4 * group.val + limb.val, by omega⟩))).getD j.val 0 = _
        exact getD_ofFn_eq _ _ _ j.isLt
      have hz' :
          ((poseidonPackedFamily B).residuals pub (rowOpenings t r) (rowSel r)).getD j.val 0 = 0 := by
        simpa [laneOf, rowOf_rowBits r] using hz
      rw [hget] at hz'
      exact hz'
    have hpose := (poseidon_packed_iff_scalar F B pub t hA).mp hposePacked
    have hcopy : CHolds copyFamily pub lam chi t := by
      intro r x hx
      simp [copyFamily] at hx
      subst x
      have hz := hrow 28 r
      simpa [laneOf, copyFamily, rowOf_rowBits r] using hz
    exact ⟨hsem.1, hsem.2.1, hsem.2.2.1, hsem.2.2.2.1,
      hsem.2.2.2.2.1, hsem.2.2.2.2.2, hpose, hcopy⟩
  · rintro ⟨hValue, hOcc, hAsset, hSchedule, hPath, hDigest, hPose, hCopy⟩ i bits
    let r := rowOf bits
    by_cases hi4 : i.val < 4
    · have hpacked : Holds (poseidonPackedFamily B) pub t :=
        (poseidon_packed_iff_scalar F B pub t hA).mpr hPose
      have hD := (list_getD_zero_iff _).mpr (hpacked r)
      have hz := hD i.val (by simpa [poseidonPackedFamily] using hi4)
      simpa [laneOf, r, hi4] using hz
    · by_cases hi28 : i.val < 28
      · let g : Fin 24 := ⟨i.val - 4, by omega⟩
        have hscalar := (scalarRows_zero_iff pub t).mpr
          ⟨hValue, hOcc, hAsset, hSchedule, hPath, hDigest⟩
        have hcomp : ∀ j : Fin 4,
            scalarLaneRow pub t r (4 * g.val + j.val) = 0 := by
          intro j
          by_cases hj : 4 * g.val + j.val < 94
          · exact hscalar r _ hj
          · have hzero : ¬ 4 * g.val + j.val < 94 := by omega
            have h12 : ¬ 4 * g.val + j.val < 12 := by omega
            have h32 : ¬ 4 * g.val + j.val < 32 := by omega
            have h49 : ¬ 4 * g.val + j.val < 49 := by omega
            have h84 : ¬ 4 * g.val + j.val < 84 := by omega
            have h92 : ¬ 4 * g.val + j.val < 92 := by omega
            simp only [scalarLaneRow, if_neg h12, if_neg h32, if_neg h49,
              if_neg h84, if_neg h92, if_neg hzero]
        have hpack : semanticPackedLane B pub t r g = 0 := by
          exact (pack4_eq_zero_iff B _ (fun j => semanticPackedLane_mem F B pub t hA hpub r g j)).mpr hcomp
        simpa [laneOf, r, hi4, hi28, g] using hpack
      · have hD := (list_getD_zero_iff _).mpr (hCopy r)
        have hz :
            (copyFamily.residuals pub lam chi (rowOpenings t r) (t 26 r) (rowSel r)).getD 0 0 = 0 := by
          exact hD 0 (by simp only [copyFamily, List.length_singleton]; omega)
        simpa [laneOf, copyFamily, r, hi4, hi28] using hz

#print axioms lanes_zero_iff_holds



private def laneBoolConsEquiv (n : Nat) :
    (Bool × (Fin n → Bool)) ≃ (Fin (n+1) → Bool) where
  toFun p := Fin.cons p.1 p.2
  invFun b := (b 0, Fin.tail b)
  left_inv p := by cases p; simp only [Fin.cons_zero, Fin.tail_cons]
  right_inv b := by
    funext i
    exact Fin.cases rfl (fun _ => rfl) i

private theorem lane_bsumB_eq_sum (n : Nat) (f : (Fin n → Bool) → K) :
    bsumB n f = ∑ b, f b := by
  classical
  induction n with
  | zero =>
      rw [bsumB, Fintype.sum_unique]
      congr 1
  | succ n ih =>
      rw [bsumB, ih, ih]
      have he : (∑ b : Fin (n+1) → Bool, f b) =
          ∑ p : Bool × (Fin n → Bool), f (Fin.cons p.1 p.2) := by
        exact (Fintype.sum_equiv (laneBoolConsEquiv n)
          (fun p => f (Fin.cons p.1 p.2)) f (fun _ => rfl)).symm
      rw [he, Fintype.sum_prod_type, Fintype.sum_bool]
      exact add_comm _ _

/-- Reindex the Boolean hypercube by the source's big-endian row address.
The proof uses the generic Boolean-sum recursion and bijectivity; it never
expands the 1024-row universe. -/
theorem bsumB_rowOf (f : Fin 1024 → K) :
    bsumB 10 (fun b => f (rowOf b)) = ∑ r : Fin 1024, f r := by
  rw [lane_bsumB_eq_sum]
  exact rowOf_bijective.sum_comp f

/-- T:1307, the H1 helper sum in row and Boolean-coordinate notation. -/
theorem lane_h1_sum (t : Trace K) :
    bsumB 10 (fun b => t 26 (rowOf b)) = ∑ r : Fin 1024, t 26 r :=
  bsumB_rowOf _

/-- T:1308, the inactive helper sum, with the source's literal 1-active
factor. This identifies the sums and does not assert that they vanish. -/
theorem lane_inactive_sum (t : Trace K) :
    bsumB 10 (fun b =>
      (1 - copyActiveLiteral (copySelectors (rowSel (rowOf b)))) * t 26 (rowOf b)) =
      ∑ r ∈ copyInactiveRows, t 26 r := by
  classical
  rw [bsumB_rowOf (fun r => (1 - copyActiveLiteral (copySelectors (rowSel r))) * t 26 r),
    copyInactiveRows, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro r _
  rw [copy_active_row]
  by_cases hr : CopyActiveRow r
  · simp only [if_pos hr, if_neg (not_not.mpr hr), sub_self, zero_mul]
  · simp only [if_neg hr, if_pos hr, sub_zero, one_mul]

#print axioms laneBoolConsEquiv
#print axioms lane_bsumB_eq_sum
#print axioms bsumB_rowOf
#print axioms lane_h1_sum
#print axioms lane_inactive_sum
end R0P
