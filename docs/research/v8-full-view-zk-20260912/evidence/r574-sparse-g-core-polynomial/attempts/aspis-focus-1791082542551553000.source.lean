import AspisV8R19.SparseGCoreInverse
import AspisV8R17.WeightedScatter
import AspisV8R17.SourceScatter
import AspisV8R19.SparseGPolynomial

set_option autoImplicit false
namespace AspisV8R19.R574SparseGCorePolynomial

open AspisR19.SparseGCoreInverse AspisV8R17 AspisR19.SparseGPolynomial

variable {F : Type*} [Field F] [NeZero (2 : F)]

def ch (s : Nat) (x : Fin 271 → F) (r : Nat) : F :=
  if r % 4 = 0 then channel (extend x) (r / 4) s else 0

def nz (x : Fin 271 → F) (r : Nat) : F :=
  if r % 4 = 0 then 0 else channel (extend x) (r / 4) (r % 4)

def weightedQ (alpha : F) (x : Fin 271 → F) (r : Nat) : F :=
  nz x r - alpha * ch 1 x r - alpha ^ 2 * ch 2 x r - alpha ^ 3 * ch 3 x r

theorem weightedQ_one (x : Fin 271 → F) (r : Nat) :
    weightedQ 1 x r = quotient (extend x) r := by
  by_cases hr : r % 4 = 0
  · simp [weightedQ, nz, ch, quotient, hr]
    ring
  · simp [weightedQ, nz, ch, quotient, hr]

def coreMap (half alpha a b c : F) (x : Fin 271 → F) (i : Fin 271) : F :=
  sourceChord half (weightedQ alpha x) a b c (128 + 3 * i.val)

theorem coreMap_witness (half : F) (x : Fin 271 → F) (i : Fin 271) :
    coreMap half 1 2 0 0 x i = (2 : F) * finiteBlock x i := by
  rw [coreMap, weightedQ_one]
  have hi : 128 + 3 * i.val < 1024 := by omega
  rw [SparseGPolynomial.source_scalar half 2 (extend x) (128 + 3 * i.val) hi]
  rw [source_block]
  rfl

#print axioms weightedQ_one
#print axioms coreMap_witness
end AspisV8R19.R574SparseGCorePolynomial
