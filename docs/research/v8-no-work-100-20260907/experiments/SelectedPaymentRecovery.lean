import AspisFormal.ArithmetizationCore

/-! Deterministic selected pair-forest amount recovery. This is a port of the
V7 dependency's field/range theorem, not a port of the V7 accepted-path theorem.
The hypotheses are exact individual value/copy/public-asset residuals; proof
acceptance enforcing them remains an explicit upstream obligation. -/
set_option autoImplicit false
namespace AspisV8.SelectedPaymentRecovery
open AspisFormal.ArithmetizationCore

abbrev Table := Nat → Nat → F
def sourceRow : Fin 3 → Nat := ![44, 460, 508]
def valueBase (which : Fin 3) : Nat := 1008 + 2 * which.val
def bitCell (which : Fin 3) (bit : Fin 30) : Nat × Nat :=
  let base := valueBase which
  (if bit.val < 10 then base else if bit.val < 20 then base + 1
    else Nat.xor base 12, bit.val % 10)
def bitValue (t : Table) (which : Fin 3) (bit : Fin 30) : F :=
  t (bitCell which bit).1 (bitCell which bit).2
def sourceValue (t : Table) (which : Fin 3) : F := t (sourceRow which) 0
def decodedValue (t : Table) (which : Fin 3) : Nat := (sourceValue t which).val

/-- Exactly the 90 Boolean, three direct recomposition and three transfer
ValueSource copy residuals. No mask/zero-padding residual is imposed. -/
structure ValueResiduals (t : Table) : Prop where
  boolean : ∀ which bit, bitValue t which bit * (bitValue t which bit - 1) = 0
  recomposition : ∀ which, t (valueBase which) 10 -
    ∑ bit : Fin 30, bitValue t which bit * (2 : F)^bit.val = 0
  sourceCopy : ∀ which, sourceValue t which - t (valueBase which) 10 = 0

/-- Four exact forest-translated copy edges and both local conservation
residuals. PrivateTransferOnly ValueSource is included above with weight one. -/
structure ConservationResiduals (t : Table) : Prop where
  inputCopy : t 1008 10 - t 1014 0 = 0
  recipientCopy : t 1010 10 - t 1014 1 = 0
  changeCopy : t 1012 10 - t 1015 1 = 0
  partialCopy : t 1014 2 - t 1015 0 = 0
  first : t 1014 2 - (t 1014 0 - t 1014 1) = 0
  second : t 1015 0 - t 1015 1 = 0

def limbBit (limb : Fin 3) (bit : Fin 10) : Fin 30 :=
  ⟨10 * limb.val + bit.val, by omega⟩

theorem split_thirty {K : Type*} [AddCommMonoid K] (f : Fin 30 → K) :
    (∑ i : Fin 30, f i) = ∑ l : Fin 3, ∑ b : Fin 10, f (limbBit l b) := by
  rw [Fin.sum_univ_three]
  have h₀ := @Fin.sum_univ_add K _ 10 20 f
  have h₁ := @Fin.sum_univ_add K _ 10 10 (fun i : Fin 20 => f (Fin.natAdd 10 i))
  rw [h₀, h₁]
  simp only [limbBit, Fin.val_zero, Fin.val_one, Fin.val_two, mul_zero, zero_add,
    add_assoc]
  congr 1

/-- The old three-limb theorem is reused by constructing virtual limbs from
the selected direct 30-bit cells. No limb columns are invented or transmitted. -/
def rangeView (t : Table) (which : Fin 3) : RangeWitness where
  bit l b := bitValue t which (limbBit l b)
  limb l := ∑ b : Fin 10, bitValue t which (limbBit l b) * (2 : F)^b.val
  value := t (valueBase which) 10

theorem selected_residuals_imply_v7_range (t : Table) (h : ValueResiduals t)
    (which : Fin 3) : RangeResiduals (rangeView t which) := by
  refine ⟨fun l b => h.boolean which (limbBit l b), fun _ => rfl, ?_⟩
  change t (valueBase which) 10 = _
  rw [sub_eq_zero.mp (h.recomposition which)]
  rw [split_thirty]
  apply Finset.sum_congr rfl
  intro l _
  simp only [rangeView, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro b _
  simp only [limbBit, pow_add, mul_assoc]
  ring

/-- The actual decoder reads canonical source-cell representatives. Their
30-bit bound is derived, not assumed, and no honest-table equality is used. -/
theorem decoded_amount_bound (t : Table) (h : ValueResiduals t) (which : Fin 3) :
    decodedValue t which < 2^30 := by
  obtain ⟨v, hv, he⟩ := range_value_sound (rangeView t which)
    (selected_residuals_imply_v7_range t h which)
  have hs : sourceValue t which = (v : F) :=
    (sub_eq_zero.mp (h.sourceCopy which)).trans he
  unfold decodedValue
  rw [hs, ZMod.val_natCast_of_lt (show v < p by change v < 2147483647; omega)]
  exact hv

theorem field_conservation (t : Table) (h : ValueResiduals t)
    (c : ConservationResiduals t) :
    sourceValue t 0 = sourceValue t 1 + sourceValue t 2 := by
  have s₀ := sub_eq_zero.mp (h.sourceCopy 0)
  have s₁ := sub_eq_zero.mp (h.sourceCopy 1)
  have s₂ := sub_eq_zero.mp (h.sourceCopy 2)
  have c₀ := sub_eq_zero.mp c.inputCopy
  have c₁ := sub_eq_zero.mp c.recipientCopy
  have c₂ := sub_eq_zero.mp c.changeCopy
  have cp := sub_eq_zero.mp c.partialCopy
  have cf := sub_eq_zero.mp c.first
  have cs := sub_eq_zero.mp c.second
  norm_num [valueBase] at s₀ s₁ s₂
  linear_combination s₀ - s₁ - s₂ + c₀ - c₁ - c₂ + cp - cf + cs

/-- Port of V7's no-wrap bridge to the selected transfer's two outputs.
Both output amounts are decoded from C1; neither is a public fee parameter. -/
theorem decoded_transfer_conservation (t : Table) (h : ValueResiduals t)
    (c : ConservationResiduals t) :
    decodedValue t 0 = decodedValue t 1 + decodedValue t 2 := by
  have h₀ := decoded_amount_bound t h 0
  have h₁ := decoded_amount_bound t h 1
  have h₂ := decoded_amount_bound t h 2
  apply nat_of_field_eq (show decodedValue t 0 < p by change _ < 2147483647; omega)
    (show decodedValue t 1 + decodedValue t 2 < p by change _ < 2147483647; omega)
  simpa only [Nat.cast_add, decodedValue, ZMod.natCast_zmod_val] using
    field_conservation t h c

/-- This is the precise mathematical precondition for the Rust u32
checked_add: it cannot overflow after the three selected range checks. -/
theorem decoded_output_sum_fits_u32 (t : Table) (h : ValueResiduals t) :
    decodedValue t 1 + decodedValue t 2 < 2^32 := by
  have h₁ := decoded_amount_bound t h 1
  have h₂ := decoded_amount_bound t h 2
  omega

/-- A parser-proved canonical raw M31 limb is exactly the representative the
Rust witness decoder reads. This closes the field-vs-u32 value convention. -/
theorem raw_decoder_representative (raw : Nat) (canonical : raw < p) :
    (raw : F).val = raw := ZMod.val_natCast_of_lt canonical

def fieldTable (raw : Nat → Nat → Nat) : Table := fun row col => (raw row col : F)

theorem raw_selected_amounts_sound (raw : Nat → Nat → Nat)
    (canonical : ∀ which, raw (sourceRow which) 0 < p)
    (h : ValueResiduals (fieldTable raw))
    (c : ConservationResiduals (fieldTable raw)) :
    (∀ which, raw (sourceRow which) 0 < 2^30) ∧
      raw 44 0 = raw 460 0 + raw 508 0 := by
  have valueExact : ∀ which, decodedValue (fieldTable raw) which =
      raw (sourceRow which) 0 := by
    intro which
    exact raw_decoder_representative _ (canonical which)
  constructor
  · intro which
    rw [← valueExact which]
    exact decoded_amount_bound _ h which
  · have balance := decoded_transfer_conservation _ h c
    rw [valueExact 0, valueExact 1, valueExact 2] at balance
    exact balance

theorem selected_asset_bindings (t : Table) (asset : F)
    (h : ∀ which, t (sourceRow which) 1 - asset = 0) :
    t 44 1 = asset ∧ t 460 1 = asset ∧ t 508 1 = asset := by
  exact ⟨sub_eq_zero.mp (h 0), sub_eq_zero.mp (h 1), sub_eq_zero.mp (h 2)⟩

theorem source_and_auxiliary_cells_pinned :
    sourceRow 0 = 44 ∧ sourceRow 1 = 460 ∧ sourceRow 2 = 508 ∧
    valueBase 0 = 1008 ∧ valueBase 1 = 1010 ∧ valueBase 2 = 1012 ∧
    bitCell 0 ⟨20, by omega⟩ = (1020, 0) ∧
    bitCell 1 ⟨20, by omega⟩ = (1022, 0) ∧
    bitCell 2 ⟨20, by omega⟩ = (1016, 0) := by decide

/-- Deliberate boundary falsifier: the selected amount constraints do not
alone imply strict positivity required by the pair trace compiler. This is
not a full semantic trace or an accepting-payment strategy. -/
theorem zero_amount_slice_satisfies_residuals :
    ValueResiduals (fun _ _ => 0) ∧ ConservationResiduals (fun _ _ => 0) ∧
      decodedValue (fun _ _ => 0) 1 = 0 := by
  constructor
  · constructor <;> intros <;> simp [bitValue, sourceValue]
  constructor
  · constructor <;> simp
  · rfl

#print axioms selected_residuals_imply_v7_range
#print axioms decoded_amount_bound
#print axioms field_conservation
#print axioms decoded_transfer_conservation
#print axioms decoded_output_sum_fits_u32
#print axioms raw_selected_amounts_sound
#print axioms selected_asset_bindings
#print axioms source_and_auxiliary_cells_pinned
#print axioms zero_amount_slice_satisfies_residuals
end AspisV8.SelectedPaymentRecovery
