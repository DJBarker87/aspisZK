import R0C.ModuloCounting
import AspisV8R19.R599CanonicalFieldTuple
import WideTower
import Mathlib.Algebra.BigOperators.Fin

/-! Proposed 32-byte rejection-free field sampler. See FS_LOG before use.
This does not replace the retained canonical-limb retry implementation. -/
set_option autoImplicit false
namespace R0C.ModuloField
open AspisV8R19.SourceDuplexStep AspisV8R19.DuplexFrames
open AspisV8R19.R599CanonicalFieldTuple AspisV8R19.SamplerFieldDecode
open AspisV8R19.OracleResampling AspisV8R19.CausalFirstHitUnionBound
open AspisWideTower AspisCircleGroupOrder
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

/-- All 32 bytes, with byte zero least significant. -/
def blockRank : State ≃ Fin (256^32) := finFunctionFinEquiv

theorem blockRank_value (s : State) :
    (blockRank s).val = ∑ i : Fin 32, (s i).val * 256^i.val :=
  finFunctionFinEquiv_apply s

def splitDigits : (Fin 8 → Fin P) ≃ (Fin 4 → Fin P) × (Fin 4 → Fin P) where
  toFun x := (fun i => x (Fin.castAdd 4 i), fun i => x (Fin.natAdd 4 i))
  invFun x := Fin.append x.1 x.2
  left_inv := by intro x; funext i; fin_cases i <;> rfl
  right_inv := by
    intro x
    apply Prod.ext <;> funext i <;> fin_cases i <;> rfl

/-- R599's four-limb decoder in each tower coordinate. -/
def digitsField : (Fin 8 → Fin P) ≃ WideExact :=
  splitDigits.trans ((Equiv.prodCongr tupleFieldEquiv tupleFieldEquiv).trans
    (QuadraticAlgebra.equivProd wideU 0).symm)

theorem digitsField_apply (x : Fin 8 → Fin P) :
    digitsField x = ⟨decode4 (x 0).val (x 1).val (x 2).val (x 3).val,
      decode4 (x 4).val (x 5).val (x 6).val (x 7).val⟩ := rfl

/-- Base-P positional rank, not the field's natural-number cast. -/
def fieldRank : Fin (P^8) ≃ WideExact := finFunctionFinEquiv.symm.trans digitsField

theorem fieldRank_zero : fieldRank 0 = 0 := by
  have hz : (finFunctionFinEquiv (fun _ : Fin 8 => (0 : Fin P))) = 0 := by
    apply Fin.ext
    simp
  rw [fieldRank, Equiv.trans_apply, ← hz, Equiv.symm_apply_apply]
  rfl

def positiveRanks (n : Nat) (hn : 0 < n) : Fin (n-1) ≃ {x : Fin n // x ≠ ⟨0, hn⟩} where
  toFun x := ⟨⟨x.val+1, by omega⟩, by intro h; have := congrArg Fin.val h; simp at this⟩
  invFun x := ⟨x.val.val-1, by
    have hne : x.val.val ≠ 0 := fun h => x.property (Fin.ext h)
    have := x.val.isLt
    omega⟩
  left_inv := by intro x; apply Fin.ext; simp
  right_inv := by
    intro x
    apply Subtype.ext
    apply Fin.ext
    have hne : x.val.val ≠ 0 := fun h => x.property (Fin.ext h)
    simp only
    omega

def nonzeroRank : Fin (P^8-1) ≃ {x : WideExact // x ≠ 0} :=
  (positiveRanks (P^8) (by norm_num [P])).trans
    (fieldRank.subtypeEquiv (by
      intro x
      have he : fieldRank x = 0 ↔ x = 0 := by
        rw [← fieldRank_zero, Equiv.apply_eq_iff_eq]
      exact not_congr he.symm))

def ordinary (s : State) : WideExact :=
  fieldRank (ModuloCounting.reduce (by norm_num [P]) (blockRank s))

def gammaNZ (s : State) : {x : WideExact // x ≠ 0} :=
  nonzeroRank (ModuloCounting.reduce (by norm_num [P]) (blockRank s))

def gamma (s : State) : WideExact := (gammaNZ s).val

theorem gamma_ne_zero (s : State) : gamma s ≠ 0 := (gammaNZ s).property

theorem ordinary_mass (y : WideExact) :
    mean (fun s => indicator (ordinary s = y)) ≤
      1 / (P^8 : ℚ) + 1 / (256^32 : ℚ) := by
  simpa only [ordinary, Nat.cast_pow, Nat.cast_ofNat] using
    ModuloCounting.encoded_mass_slack (by positivity : 0 < 256^32)
      (by norm_num [P] : 0 < P^8) blockRank fieldRank y

theorem gamma_mass (y : {x : WideExact // x ≠ 0}) :
    mean (fun s => indicator (gammaNZ s = y)) ≤
      1 / ((P^8-1 : Nat) : ℚ) + 1 / (256^32 : ℚ) := by
  simpa only [gammaNZ, Nat.cast_pow, Nat.cast_ofNat] using
    ModuloCounting.encoded_mass_slack (by positivity : 0 < 256^32)
      (by norm_num [P] : 0 < P^8-1) blockRank nonzeroRank y

/-- The exact quotient part of the fiber bound is 256 for both codomains. -/
theorem quotients : 256^32 / P^8 = 256 ∧ 256^32 / (P^8-1) = 256 := by
  norm_num [P]

theorem ordinary_mass_257 (y : WideExact) :
    mean (fun s => indicator (ordinary s = y)) ≤ 257 / (256^32 : ℚ) := by
  have h := ModuloCounting.encoded_mass_le (by norm_num [P] : 0 < P^8)
    blockRank fieldRank y
  simpa only [ordinary, quotients.1, Nat.reduceAdd, Nat.cast_pow, Nat.cast_ofNat] using h

theorem gamma_mass_257 (y : WideExact) :
    mean (fun s => indicator (gamma s = y)) ≤ 257 / (256^32 : ℚ) := by
  by_cases hy : y = 0
  · subst y
    have he (s : State) : indicator (gamma s = 0) = 0 := by
      simp only [indicator, if_neg (gamma_ne_zero s)]
    exact (mean_congr he).le.trans (by rw [mean_const]; positivity)
  · have he (s : State) : gamma s = y ↔ gammaNZ s = ⟨y,hy⟩ :=
      ⟨fun h => Subtype.ext h, fun h => congrArg Subtype.val h⟩
    have hm := ModuloCounting.encoded_mass_le (by norm_num [P] : 0 < P^8-1)
      blockRank nonzeroRank ⟨y,hy⟩
    have hm' : mean (fun s => indicator (gammaNZ s = ⟨y,hy⟩)) ≤
        257 / (256^32 : ℚ) := by
      simpa only [gammaNZ, quotients.2, Nat.reduceAdd, Nat.cast_pow, Nat.cast_ofNat] using hm
    exact (mean_congr (fun s => FS.indicator_iff (he s))).le.trans hm'

theorem ordinary_event (bad : Finset WideExact) :
    mean (fun s => indicator (ordinary s ∈ bad)) ≤ bad.card * (257 / (256^32 : ℚ)) :=
  ModuloCounting.event_mass_le ordinary _ ordinary_mass_257 bad

theorem gamma_event (bad : Finset WideExact) :
    mean (fun s => indicator (gamma s ∈ bad)) ≤ bad.card * (257 / (256^32 : ℚ)) :=
  ModuloCounting.event_mass_le gamma _ gamma_mass_257 bad

#print axioms blockRank_value
#print axioms digitsField_apply
#print axioms fieldRank_zero
#print axioms gamma_ne_zero
#print axioms ordinary_mass
#print axioms gamma_mass
#print axioms quotients
#print axioms ordinary_mass_257
#print axioms gamma_mass_257
#print axioms ordinary_event
#print axioms gamma_event
end
end R0C.ModuloField
