import AspisV8R19.R662FullIndexedMaskPreservation
import AspisV8R19.R660FullSourceResidualCorrection
import AspisV8R19.R710SelectedActivePolynomial

/-! Raw ordinary joint-observation schema for the selected source-shaped
two-swap model.  This file does not assert rank, source execution, a legal
witness construction, or a privacy property. -/
set_option autoImplicit false
namespace AspisV8R19.R738JointObservationModel

open AspisV8R16 AspisV8R17 AspisR19
open AspisR19.TwoSwapSourceTable
open AspisR19.BetaUniformCorrection
open AspisV8R19.R662FullIndexedMaskPreservation
open AspisV8R19.R660FullSourceResidualCorrection
open AspisV8R19.R710SelectedActivePolynomial
open AspisV8R19.R707FullActiveDeterminant
open scoped BigOperators
noncomputable section

variable {F : Type*}

abbrev J := R710SelectedActivePolynomial.J
abbrev Index256 := HighRepairInvariant.Index 256
abbrev ObservationRow := J ⊕ (Fin 3 ⊕ Fin 5)

section RingModel
variable [CommRing F]

/-- The exact guarded 256-by-four flattening used by the indexed source mask. -/
def rawFlatten (q : Index256 → F) (r : Nat) : F :=
  if h : r < 1024 then q (⟨r / 4, by omega⟩, ⟨r % 4, Nat.mod_lt _ (by decide)⟩) else 0

/-- One first-fold-zero pair at a full source coordinate. -/
def qPair (alpha : F) (d : Fin 255) (s : Fin 3) (r : Nat) : F :=
  unitVector (4 * d.val + s.val + 1) r - alpha ^ (s.val + 1) * unitVector (4 * d.val) r

/-- The saved diagnostic direction subtracts the same slot at block zero. -/
def direction (alpha : F) (d : Fin 255) (s : Fin 3) (r : Nat) : F :=
  qPair alpha d s r - qPair alpha 0 s r

/-- The actual R16 inverse transport applied to the selected source chord. -/
def rawMask (half a b c : F) (q : Index256 → F) : Fin 1024 → F :=
  inverseTransport TwoSwapSourceTable.inactive 1023 TwoSwapSourceTable.order
    (fun j => sourceChord half (rawFlatten q) a b c j.val)

/-- The ordinary source original weights: the `previous` channel is absent in
the `structured = false` branch, so the supplied G array is literally zero. -/
def rawOrdinaryOriginal (z : Fin 10 → F) (kappa : F) : Fin 1024 → F :=
  sourceOriginalWeight (SourceStatementPoints.points z) kappa TwoSwapSourceTable.inactive
    (fun _ => 0) false

/-- The ordinary quotient weights including all three selected image updates. -/
def rawOrdinaryWeight (half a b c kappa tau : F) (z : Fin 10 → F) : Nat → F :=
  sourceQuotientWeights half
    (extendFin1024 (transportDual TwoSwapSourceTable.inactive 1023 TwoSwapSourceTable.order
      (rawOrdinaryOriginal z kappa))) a b c tau false

/-- One exact ordinary source coefficient for the full 256-by-four quotient. -/
def rawRelation (half quarter a b c kappa tau : F) (z : Fin 10 → F)
    (q : Index256 → F) (k : Nat) : F :=
  coefficient (sourceKernel 256 k quarter) q
    (fun i => rawOrdinaryWeight half a b c kappa tau z (4 * i.1.val + i.2.val))

def relationIndex : Fin 5 → Nat
  | ⟨0, _⟩ => 1
  | ⟨1, _⟩ => 2
  | ⟨2, _⟩ => 3
  | ⟨3, _⟩ => 5
  | ⟨4, _⟩ => 6

/-- The 214 active chord rows, three point rows, and the five retained
ordinary coefficient rows used by the joint minor. -/
def rawObservation (half quarter a b c kappa tau : F) (z : Fin 10 → F)
    (q : Index256 → F) : ObservationRow → F
  | .inl j => sourceChord half (rawFlatten q) a b c (rowCode j)
  | .inr (.inl p) => sourcePointFunctional (SourceStatementPoints.points z p)
      (rawMask half a b c q)
  | .inr (.inr k) => rawRelation half quarter a b c kappa tau z q (relationIndex k)
end RingModel

section FieldCorrespondence
variable [Field F] [NeZero (2 : F)]

theorem rawFlatten_eq_flattenFull (q : Index256 → F) :
    rawFlatten q = R662FullIndexedMaskPreservation.flattenFull q := by
  rfl

theorem rawMask_eq_indexedMask (half a b c : F) (q : Index256 → F) :
    rawMask half a b c q = R662FullIndexedMaskPreservation.indexedMask half a b c q := by
  rfl

theorem rawOrdinaryWeight_eq_fullWeight (half a b c kappa tau : F)
    (z : Fin 10 → F) (previous : Fin 271 → F) (i : Index256) :
    rawOrdinaryWeight half a b c kappa tau z (4 * i.1.val + i.2.val) =
      fullWeight half a b c kappa tau z previous false i := by
  rfl

theorem rawRelation_eq_fullRelation (half quarter a b c kappa tau : F)
    (z : Fin 10 → F) (previous : Fin 271 → F) (q : Index256 → F) (k : Nat) :
    rawRelation half quarter a b c kappa tau z q k =
      fullRelation half quarter a b c kappa tau z previous false q k := by
  rfl

#print axioms rawFlatten_eq_flattenFull
#print axioms rawMask_eq_indexedMask
#print axioms rawOrdinaryWeight_eq_fullWeight
#print axioms rawRelation_eq_fullRelation
end FieldCorrespondence

end
end AspisV8R19.R738JointObservationModel
