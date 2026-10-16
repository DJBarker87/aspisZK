import ExtractedMaskQM31Exact
import ExtractedMaskTowerAdd
import ExtractedMaskReducer
import AspisV8R15.ExactTowerBase

/-! Pure arithmetic contracts for the current generated `qm31_pack_base4`.
These definitions do not model the source array or function execution. -/
set_option autoImplicit false
namespace AspisR1.ExtractedMaskQmPackBase4Arithmetic

open AspisR1.ExtractedMaskQM31Exact
open AspisR1.ExtractedMaskTowerAdd

abbrev CurrentQM := AspisR1.ExtractedMaskQM31Exact.CurrentQM
abbrev Canonical := AspisR1.ExtractedMaskQM31Exact.CurrentCanonicalQM
abbrev E := AspisV8R15.ExactTowerBase.QM31Exact
abbrev M := AspisV8R15.ExactTowerBase.M31Exact
abbrev P : Nat := AspisV8R15.ExactTowerBase.P

/-- The four source limbs of one stored QM31, in `(c0.a,c0.b,c1.a,c1.b)` order. -/
def limb (x : CurrentQM) (j : Fin 4) : Nat :=
  match j.val with
  | 0 => x.c0.a.val
  | 1 => x.c0.b.val
  | 2 => x.c1.a.val
  | _ => x.c1.b.val

theorem limb_lt_P (x : CurrentQM) (hx : Canonical x) (j : Fin 4) :
    limb x j < P := by
  have hx' : AspisR1.ExtractedMaskTowerAdd.CanonicalQM x := hx
  rcases hx' with ⟨⟨h0, h1⟩, ⟨h2, h3⟩⟩
  fin_cases j <;> simp [limb] <;> assumption

/-- Actual coefficient matrix of `1,i,u,iu` in source `(a,b)` coordinates. -/
def acc00 (v : Fin 4 → CurrentQM) : Nat :=
  limb (v 0) 0 + (P - limb (v 1) 1) + 2 * limb (v 2) 2 +
    (P - limb (v 2) 3) + (P - limb (v 3) 2) +
      (2 * P - 2 * limb (v 3) 3)

def acc01 (v : Fin 4 → CurrentQM) : Nat :=
  limb (v 0) 1 + limb (v 1) 0 + limb (v 2) 2 +
    2 * limb (v 2) 3 + 2 * limb (v 3) 2 + (P - limb (v 3) 3)

def acc10 (v : Fin 4 → CurrentQM) : Nat :=
  limb (v 0) 2 + (P - limb (v 1) 3) + limb (v 2) 0 +
    (P - limb (v 3) 1)

def acc11 (v : Fin 4 → CurrentQM) : Nat :=
  limb (v 0) 3 + limb (v 1) 2 + limb (v 2) 1 + limb (v 3) 0

theorem accumulators_lt_8P (v : Fin 4 → CurrentQM)
    (h : ∀ j, Canonical (v j)) :
    acc00 v < 8 * P ∧ acc01 v < 8 * P ∧
    acc10 v < 8 * P ∧ acc11 v < 8 * P := by
  have hb (i j : Fin 4) : limb (v i) j < P := limb_lt_P (v i) (h i) j
  have hp : 0 < P := by norm_num [P, AspisV8R17.RawReducer.P]
  have h00 := hb 0 0; have h01 := hb 0 1; have h02 := hb 0 2; have h03 := hb 0 3
  have h10 := hb 1 0; have h11 := hb 1 1; have h12 := hb 1 2; have h13 := hb 1 3
  have h20 := hb 2 0; have h21 := hb 2 1; have h22 := hb 2 2; have h23 := hb 2 3
  have h30 := hb 3 0; have h31 := hb 3 1; have h32 := hb 3 2; have h33 := hb 3 3
  unfold acc00 acc01 acc10 acc11
  constructor
  · omega
  constructor
  · omega
  constructor
  · omega
  · omega

/-- Exact tower basis elements, with `i` inside CM31 and `u` as the outer
quadratic generator. -/
def iBasis : E := ⟨⟨0, 1⟩, 0⟩
def uBasis : E := ⟨0, 1⟩
def mathematicalPack (v : Fin 4 → CurrentQM) : E :=
  decode (v 0) + iBasis * decode (v 1) +
    uBasis * decode (v 2) + (iBasis * uBasis) * decode (v 3)

def accumulatorPack (v : Fin 4 → CurrentQM) : E :=
  ⟨⟨(acc00 v : M), (acc01 v : M)⟩,
   ⟨(acc10 v : M), (acc11 v : M)⟩⟩

theorem mathematicalPack_eq_accumulatorPack (v : Fin 4 → CurrentQM)
    (h : ∀ j, Canonical (v j)) :
    mathematicalPack v = accumulatorPack v := by
  have hp : (P : M) = 0 := ZMod.natCast_self P
  have hlt (i j : Fin 4) : limb (v i) j < P := limb_lt_P (v i) (h i) j
  have cast_subP (n : Nat) (hn : n < P) : ((P - n : Nat) : M) = -(n : M) := by
    rw [Nat.cast_sub (Nat.le_of_lt hn), hp]
    simp
  have cast_sub2P (n : Nat) (hn : n < P) :
      ((2 * P - 2 * n : Nat) : M) = - (2 : M) * (n : M) := by
    have hle : 2 * n ≤ 2 * P := Nat.mul_le_mul_left 2 (Nat.le_of_lt hn)
    rw [Nat.cast_sub hle, Nat.cast_mul, Nat.cast_mul, hp]
    ring
  have hs11 : ((P - (v 1).c0.b.val : Nat) : M) = -((v 1).c0.b.val : M) :=
    cast_subP _ (hlt 1 1)
  have hs23 : ((P - (v 2).c1.b.val : Nat) : M) = -((v 2).c1.b.val : M) :=
    cast_subP _ (hlt 2 3)
  have hs32 : ((P - (v 3).c1.a.val : Nat) : M) = -((v 3).c1.a.val : M) :=
    cast_subP _ (hlt 3 2)
  have hs33 : ((P - (v 3).c1.b.val : Nat) : M) = -((v 3).c1.b.val : M) :=
    cast_subP _ (hlt 3 3)
  have hs13 : ((P - (v 1).c1.b.val : Nat) : M) = -((v 1).c1.b.val : M) :=
    cast_subP _ (hlt 1 3)
  have hs30 : ((P - (v 3).c0.b.val : Nat) : M) = -((v 3).c0.b.val : M) :=
    cast_subP _ (hlt 3 1)
  have hs2_33 : ((2 * P - 2 * (v 3).c1.b.val : Nat) : M) =
      -(2 : M) * ((v 3).c1.b.val : M) :=
    cast_sub2P (v 3).c1.b.val (hlt 3 3)
  ext <;> simp [mathematicalPack, accumulatorPack, iBasis, uBasis,
    AspisR1.ExtractedMaskQM31Exact.decode, decode, acc00, acc01, acc10, acc11,
    limb, hp, hs11, hs23, hs32, hs33, hs13, hs30, hs2_33]
  all_goals ring

/-- The four source reducers' canonical representatives reconstruct the
literal exact-tower coordinate pack. This is the final-coordinate algebra
adapter; successful evaluation of the generated caller is a separate theorem. -/
theorem reducedOutput_decode_eq_accumulatorPack
    (v : Fin 4 → CurrentQM)
    (o00 o01 o10 o11 : AspisR1SelectedMaskProbe.field.M31)
    (h00 : o00.val = acc00 v % P)
    (h01 : o01.val = acc01 v % P)
    (h10 : o10.val = acc10 v % P)
    (h11 : o11.val = acc11 v % P) :
    AspisR1.ExtractedMaskQM31Exact.decode
        (⟨⟨o00, o01⟩, ⟨o10, o11⟩⟩ : CurrentQM) = accumulatorPack v := by
  ext <;> simp [AspisR1.ExtractedMaskQM31Exact.decode, accumulatorPack,
    h00, h01, h10, h11, ZMod.natCast_mod]

#print axioms limb_lt_P
#print axioms accumulators_lt_8P
#print axioms mathematicalPack_eq_accumulatorPack
#print axioms reducedOutput_decode_eq_accumulatorPack
end AspisR1.ExtractedMaskQmPackBase4Arithmetic
