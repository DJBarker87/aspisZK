import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Ring
import AspisV8R17.QM31WordTower
import AspisV8R17.RawReducerNat

set_option autoImplicit false
namespace AspisR1.R22RawQmProductResidues

abbrev M := AspisV8R17.QM31WordResidues.M
abbrev Q := AspisV8R17.QM31WordResidues.Q
open AspisV8R17.QM31WordResidues
open AspisV8R17.RawReducer

def sourceU (a b c d e f g h : M) : M := c*g-d*h
def sourceV (a b c d e f g h : M) : M := c*h+d*g

def sourceCoefficients (a b c d e f g h : M) : M × M × M × M :=
  let u := sourceU a b c d e f g h
  let v := sourceV a b c d e f g h
  (a*e-b*f+2*u-v,
   a*f+b*e+u+2*v,
   a*g+c*e-b*h-d*f,
   a*h+b*g+c*f+d*e)

def qmulCoefficients (x y : Q) : M × M × M × M :=
  let z := qMul x y
  (z.1.1, z.1.2, z.2.1, z.2.2)

theorem source_coefficients_eq_qmul (a b c d e f g h : M) :
    sourceCoefficients a b c d e f g h =
      qmulCoefficients ((a,b),(c,d)) ((e,f),(g,h)) := by
  simp [sourceCoefficients, sourceU, sourceV, qmulCoefficients,
    qMul, cMul, cAdd, cSub, cR]
  constructor
  · ring
  constructor
  · ring
  constructor
  · ring
  · ring

def rawU (c d g h : Nat) : Nat :=
  foldBits (c*g + P*P - d*h)
def rawV (c d g h : Nat) : Nat :=
  foldBits (c*h + d*g)
def rawC0 (a b c d e f g h : Nat) : Nat :=
  a*e + P*P - b*f + 2*rawU c d g h + 3*P - rawV c d g h
def rawC1 (a b c d e f g h : Nat) : Nat :=
  a*f + b*e + rawU c d g h + 2*rawV c d g h
def rawC2 (a b c d e f g h : Nat) : Nat :=
  a*g + c*e + 2*P*P - b*h - d*f
def rawC3 (a b c d e f g h : Nat) : Nat :=
  a*h + b*g + c*f + d*e

def rawCoefficients (a b c d e f g h : Nat) : Nat × Nat × Nat × Nat :=
  (rawC0 a b c d e f g h, rawC1 a b c d e f g h,
   rawC2 a b c d e f g h, rawC3 a b c d e f g h)

theorem foldBits_cast (n : Nat) : (foldBits n : M) = (n : M) := by
  rw [foldBits_eq_fold31]
  have hm := congrArg (fun k : Nat => (k : M)) (fold31_mod n)
  simpa only [ZMod.natCast_mod] using hm

theorem cast_P_zero : (P : M) = 0 := by
  change ((2147483647 : Nat) : ZMod 2147483647) = 0
  exact ZMod.natCast_self _

theorem cast_P_sq_zero : ((P * P : Nat) : M) = 0 := by
  change (P : M) * (P : M) = 0
  rw [cast_P_zero]
  simp

theorem cast_two_P_sq_zero : ((2 * P * P : Nat) : M) = 0 := by
  change (2 : M) * (P : M) * (P : M) = 0
  rw [cast_P_zero]
  simp

theorem rawU_cast (c d g h : Nat) (hunder : d*h ≤ c*g + P*P) :
    (rawU c d g h : M) = (c : M)*(g : M) - (d : M)*(h : M) := by
  unfold rawU
  rw [foldBits_cast, Nat.cast_sub hunder]
  simp only [Nat.cast_add, Nat.cast_mul]
  rw [cast_P_zero]
  simp only [zero_mul, mul_zero, add_zero, sub_zero]

theorem rawV_cast (c d g h : Nat) :
    (rawV c d g h : M) = (c : M)*(h : M) + (d : M)*(g : M) := by
  unfold rawV
  rw [foldBits_cast]
  simp only [Nat.cast_add, Nat.cast_mul]

theorem rawC0_cast (a b c d e f g h : Nat)
    (hunderU : d*h ≤ c*g + P*P)
    (hunderA : b*f ≤ a*e + P*P)
    (hunderB : rawV c d g h ≤ a*e + P*P - b*f + 2*rawU c d g h + 3*P) :
    (rawC0 a b c d e f g h : M) =
      (a:M)*(e:M) - (b:M)*(f:M) +
        2*((c:M)*(g:M) - (d:M)*(h:M)) -
        ((c:M)*(h:M) + (d:M)*(g:M)) := by
  unfold rawC0
  rw [Nat.cast_sub hunderB]
  simp only [Nat.cast_add, Nat.cast_mul]
  rw [Nat.cast_sub hunderA]
  rw [Nat.cast_add, cast_P_sq_zero]
  simp only [Nat.cast_mul]
  rw [rawU_cast c d g h hunderU, rawV_cast c d g h]
  rw [cast_P_zero]
  simp only [mul_zero, add_zero, sub_zero]
  ring

theorem rawC1_cast (a b c d e f g h : Nat) (hunderU : d*h ≤ c*g + P*P) :
    (rawC1 a b c d e f g h : M) =
      (a:M)*(f:M) + (b:M)*(e:M) +
        ((c:M)*(g:M) - (d:M)*(h:M)) +
        2*((c:M)*(h:M) + (d:M)*(g:M)) := by
  unfold rawC1
  simp only [Nat.cast_add, Nat.cast_mul]
  rw [rawU_cast c d g h hunderU, rawV_cast c d g h]
  ring

theorem rawC2_cast (a b c d e f g h : Nat)
    (hunderA : b*h ≤ a*g + c*e + 2*P*P)
    (hunderB : d*f ≤ a*g + c*e + 2*P*P - b*h) :
    (rawC2 a b c d e f g h : M) =
      (a:M)*(g:M) + (c:M)*(e:M) - (b:M)*(h:M) - (d:M)*(f:M) := by
  unfold rawC2
  rw [Nat.cast_sub hunderB, Nat.cast_sub hunderA]
  simp only [Nat.cast_add, Nat.cast_mul]
  rw [cast_P_zero]
  simp only [mul_zero, add_zero]

theorem rawC3_cast (a b c d e f g h : Nat) :
    (rawC3 a b c d e f g h : M) =
      (a:M)*(h:M) + (b:M)*(g:M) + (c:M)*(f:M) + (d:M)*(e:M) := by
  unfold rawC3
  norm_cast

def castNatQuartet (x : Nat × Nat × Nat × Nat) : M × M × M × M :=
  ((x.1 : M), ((x.2.1 : M), ((x.2.2.1 : M), (x.2.2.2 : M))))

theorem raw_coefficients_eq_qmul (a b c d e f g h : Nat)
    (hunderU : d*h ≤ c*g + P*P)
    (hunder0a : b*f ≤ a*e + P*P)
    (hunder0b : rawV c d g h ≤ a*e + P*P - b*f + 2*rawU c d g h + 3*P)
    (hunder2a : b*h ≤ a*g + c*e + 2*P*P)
    (hunder2b : d*f ≤ a*g + c*e + 2*P*P - b*h) :
    castNatQuartet (rawCoefficients a b c d e f g h) =
      qmulCoefficients ((a,b),(c,d)) ((e,f),(g,h)) := by
  have h0 := rawC0_cast a b c d e f g h hunderU hunder0a hunder0b
  have h1 := rawC1_cast a b c d e f g h hunderU
  have h2 := rawC2_cast a b c d e f g h hunder2a hunder2b
  have h3 := rawC3_cast a b c d e f g h
  have hs : castNatQuartet (rawCoefficients a b c d e f g h) =
      sourceCoefficients (a:M) (b:M) (c:M) (d:M) (e:M) (f:M) (g:M) (h:M) := by
    apply Prod.ext
    · exact h0
    · apply Prod.ext
      · exact h1
      · apply Prod.ext
        · exact h2
        · exact h3
  rw [hs]
  exact source_coefficients_eq_qmul _ _ _ _ _ _ _ _

#print axioms source_coefficients_eq_qmul
#print axioms foldBits_cast
#print axioms rawU_cast
#print axioms rawV_cast
#print axioms rawC0_cast
#print axioms rawC1_cast
#print axioms rawC2_cast
#print axioms rawC3_cast
#print axioms raw_coefficients_eq_qmul
end AspisR1.R22RawQmProductResidues
