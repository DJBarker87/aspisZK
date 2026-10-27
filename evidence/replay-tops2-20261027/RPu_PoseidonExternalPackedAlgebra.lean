import RPu_RawPoseidonRowField
import RPu_ExtractedMaskQmPackBase4Arithmetic

/-! Symbolic algebra for the actual external packed helper. The coefficient
formulas reuse the towerPackWeight matrix of V5CuArithmeticEquivalences and
the maintained raw_rows_decode_eq_poseidonMat4 theorem. Natural subtraction
follows the source order and is justified by explicit bounds. Source execution
is a separate consumer, not an assumption hidden in this arithmetic bridge. -/
set_option autoImplicit false
namespace AspisR1.PoseidonExternalPackedAlgebra
open AspisR1.RawPoseidonRowField (M Q decodeWords)
open AspisR1.RawPoseidonExternalRows (rawRowNat)
open AspisR1.ExtractedMaskQmPackBase4Arithmetic (iBasis uBasis)
open AspisV8R15.ExactTowerBase (P)

def packedNat (bound : Nat) (w : Fin 4 → Fin 4 → Nat) (j : Fin 4) : Nat :=
  match j.val with
  | 0 => ((((w 0 0 + 5 * bound - w 1 1) + 2 * w 2 2 - w 2 3) - w 3 2) - 2 * w 3 3)
  | 1 => w 0 1 + w 1 0 + w 2 2 + 2 * w 2 3 + 2 * w 3 2 + bound - w 3 3
  | 2 => (w 0 2 + 2 * bound - w 1 3) + w 2 0 - w 3 1
  | _ => w 0 3 + w 1 2 + w 2 1 + w 3 0

def packedCoordinates (w : Fin 4 → Fin 4 → M) (j : Fin 4) : M :=
  match j.val with
  | 0 => w 0 0 - w 1 1 + 2 * w 2 2 - w 2 3 - w 3 2 - 2 * w 3 3
  | 1 => w 0 1 + w 1 0 + w 2 2 + 2 * w 2 3 + 2 * w 3 2 - w 3 3
  | 2 => w 0 2 - w 1 3 + w 2 0 - w 3 1
  | _ => w 0 3 + w 1 2 + w 2 1 + w 3 0

def fieldWords (w : Fin 4 → M) : Q := ⟨⟨w 0,w 1⟩,⟨w 2,w 3⟩⟩

theorem packed_coordinates_eq_tower_pack (w : Fin 4 → Fin 4 → Nat) :
    fieldWords (packedCoordinates (fun r j => (w r j : M))) =
      R0P.poseidonPackingFormula iBasis uBasis (fun r => decodeWords (w r)) := by
  ext <;> simp [fieldWords,packedCoordinates,decodeWords,
    R0P.poseidonPackingFormula,iBasis,uBasis] <;> ring

theorem packed_nat_cast (bound : Nat) (w : Fin 4 → Fin 4 → Nat)
    (hb : ∀ r j, w r j < bound) (hbound : (bound : M) = 0) (j : Fin 4) :
    (packedNat bound w j : M) = packedCoordinates (fun r k => (w r k : M)) j := by
  have h11 := hb 1 1
  have h23 := hb 2 3
  have h32 := hb 3 2
  have h33 := hb 3 3
  have h13 := hb 1 3
  have h31 := hb 3 1
  fin_cases j
  · change (((((w 0 0 + 5 * bound - w 1 1) + 2 * w 2 2 - w 2 3) - w 3 2) - 2 * w 3 3 : Nat) : M) = _
    have hfirst : w 1 1 ≤ w 0 0 + 5 * bound := by omega
    rw [← Nat.sub_add_comm hfirst]
    rw [Nat.sub_sub,Nat.sub_sub,Nat.sub_sub]
    have htotal : w 1 1 + (w 2 3 + (w 3 2 + 2 * w 3 3)) ≤ w 0 0 + 5 * bound + 2 * w 2 2 := by omega
    rw [Nat.cast_sub htotal]
    simp only [Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat,hbound]
    change _ = (w 0 0 : M) - (w 1 1 : M) + 2 * (w 2 2 : M) - (w 2 3 : M) - (w 3 2 : M) - 2 * (w 3 3 : M)
    ring
  · change (((w 0 1 + w 1 0 + w 2 2 + 2 * w 2 3 + 2 * w 3 2 + bound - w 3 3 : Nat) : M)) = _
    have htotal : w 3 3 ≤ w 0 1 + w 1 0 + w 2 2 + 2 * w 2 3 + 2 * w 3 2 + bound := by omega
    rw [Nat.cast_sub htotal]
    simp only [Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat,hbound]
    change _ = (w 0 1 : M) + (w 1 0 : M) + (w 2 2 : M) + 2 * (w 2 3 : M) + 2 * (w 3 2 : M) - (w 3 3 : M)
    ring
  · change ((((w 0 2 + 2 * bound - w 1 3) + w 2 0 - w 3 1 : Nat) : M)) = _
    have hfirst : w 1 3 ≤ w 0 2 + 2 * bound := by omega
    rw [← Nat.sub_add_comm hfirst,Nat.sub_sub]
    have htotal : w 1 3 + w 3 1 ≤ w 0 2 + 2 * bound + w 2 0 := by omega
    rw [Nat.cast_sub htotal]
    simp only [Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat,hbound]
    change _ = (w 0 2 : M) - (w 1 3 : M) + (w 2 0 : M) - (w 3 1 : M)
    ring
  · change (((w 0 3 + w 1 2 + w 2 1 + w 3 0 : Nat) : M)) = _
    simp only [Nat.cast_add]
    rfl

theorem packed_nat_decode (bound : Nat) (w : Fin 4 → Fin 4 → Nat)
    (hb : ∀ r j, w r j < bound) (hbound : (bound : M) = 0) :
    decodeWords (packedNat bound w) =
      R0P.poseidonPackingFormula iBasis uBasis (fun r => decodeWords (w r)) := by
  have hcast : (fun j => (packedNat bound w j : M)) =
      packedCoordinates (fun r j => (w r j : M)) := funext (packed_nat_cast bound w hb hbound)
  change fieldWords (fun j => (packedNat bound w j : M)) = _
  rw [hcast,packed_coordinates_eq_tower_pack]

theorem packed_nat_lt_eight_bound (bound : Nat) (w : Fin 4 → Fin 4 → Nat)
    (hb : ∀ r j, w r j < bound) (j : Fin 4) : packedNat bound w j < 8 * bound := by
  have h00 := hb 0 0; have h01 := hb 0 1; have h02 := hb 0 2; have h03 := hb 0 3
  have h10 := hb 1 0; have h11 := hb 1 1; have h12 := hb 1 2; have h13 := hb 1 3
  have h20 := hb 2 0; have h21 := hb 2 1; have h22 := hb 2 2; have h23 := hb 2 3
  have h30 := hb 3 0; have h31 := hb 3 1; have h32 := hb 3 2; have h33 := hb 3 3
  fin_cases j <;> simp only [packedNat] <;> omega

theorem raw_rows_lt_seven_P (w : Fin 4 → Fin 4 → Nat)
    (hw : ∀ r j, w r j < P) (r j : Fin 4) :
    rawRowNat (fun i => w i j) r < 7 * P := by
  have h0 := hw 0 j; have h1 := hw 1 j; have h2 := hw 2 j; have h3 := hw 3 j
  fin_cases r <;> simp only [rawRowNat] <;> omega

theorem packed_raw_rows_decode (w : Fin 4 → Fin 4 → Nat)
    (hw : ∀ r j, w r j < P) :
    decodeWords (packedNat (7 * P) (fun r j => rawRowNat (fun i => w i j) r)) =
      R0P.poseidonPackingFormula iBasis uBasis
        (R0P.poseidonMat4 (fun r => decodeWords (w r))) := by
  have hb : ((7 * P : Nat) : M) = 0 := by
    rw [Nat.cast_mul,ZMod.natCast_self]
    ring
  rw [packed_nat_decode (7 * P) _ (raw_rows_lt_seven_P w hw) hb]
  exact congrArg (R0P.poseidonPackingFormula iBasis uBasis)
    (funext (fun r => AspisR1.RawPoseidonRowField.raw_rows_decode_eq_poseidonMat4 w r))

#print axioms packed_coordinates_eq_tower_pack
#print axioms packed_nat_cast
#print axioms packed_nat_decode
#print axioms packed_nat_lt_eight_bound
#print axioms raw_rows_lt_seven_P
#print axioms packed_raw_rows_decode
end AspisR1.PoseidonExternalPackedAlgebra
