module
public import AspisV8R17.QM31WordFormulas
public import Mathlib.Data.ZMod.Basic
import Lean.Elab.Tactic.Omega

/-! Coordinatewise residue interface for the retained explicit tower.
This leaf does not instantiate its quadratic-algebra operations or fields. -/
@[expose] public section
namespace AspisV8R17.QM31WordResidues
open RawReducer GeneratedQM31Products GeneratedQM31Linear
abbrev M := ZMod P
abbrev C := M × M
abbrev Q := C × C
def decodeC (x : WordPair) : C := ⟨(x.1 : M),(x.2 : M)⟩
def decodeQ (x : WordPair × WordPair) : Q := ⟨decodeC x.1,decodeC x.2⟩
def CanonicalPair (x : WordPair) : Prop := x.1<P ∧ x.2<P

theorem decode_add (x y : WordPair) :
    decodeC (addWords x y) =
      ((decodeC x).1+(decodeC y).1,(decodeC x).2+(decodeC y).2) := by
  apply Prod.ext <;> simp [decodeC, addWords]

theorem sub_cast (a b : Nat) (hb : b<P) :
    (((a+P-b)%P : Nat) : M) = (a : M)-(b : M) := by
  have h : b ≤ a+P := by omega
  rw [ZMod.natCast_mod, Nat.cast_sub h, Nat.cast_add, ZMod.natCast_self, add_zero]

theorem decode_sub (x y : WordPair) (hy : CanonicalPair y) :
    decodeC (subWords x y) =
      ((decodeC x).1-(decodeC y).1,(decodeC x).2-(decodeC y).2) := by
  apply Prod.ext
  · exact sub_cast _ _ hy.1
  · exact sub_cast _ _ hy.2

theorem decode_qm_add (x y : WordPair × WordPair) :
    decodeQ (qmAddWords x y) =
      (((decodeQ x).1.1+(decodeQ y).1.1,(decodeQ x).1.2+(decodeQ y).1.2),
       ((decodeQ x).2.1+(decodeQ y).2.1,(decodeQ x).2.2+(decodeQ y).2.2)) := by
  apply Prod.ext
  · exact decode_add _ _
  · exact decode_add _ _

theorem decode_qm_sub (x y : WordPair × WordPair)
    (hy : CanonicalPair y.1 ∧ CanonicalPair y.2) :
    decodeQ (qmSubWords x y) =
      (((decodeQ x).1.1-(decodeQ y).1.1,(decodeQ x).1.2-(decodeQ y).1.2),
       ((decodeQ x).2.1-(decodeQ y).2.1,(decodeQ x).2.2-(decodeQ y).2.2)) := by
  apply Prod.ext
  · exact decode_sub _ _ hy.1
  · exact decode_sub _ _ hy.2

def cAdd (x y : C) : C := (x.1+y.1,x.2+y.2)
def cSub (x y : C) : C := (x.1-y.1,x.2-y.2)
def cMul (x y : C) : C :=
  (x.1*y.1-x.2*y.2,(x.1+x.2)*(y.1+y.2)-x.1*y.1-x.2*y.2)
def cR (x : C) : C := (x.1+x.1-x.2,x.1+(x.2+x.2))

theorem mul_canonical (x y : WordPair) : CanonicalPair (mulWords x y) := by
  constructor <;> exact Nat.mod_lt _ (by decide)

theorem decode_mul (x y : WordPair) :
    decodeC (mulWords x y) = cMul (decodeC x) (decodeC y) := by
  apply Prod.ext
  · change (((((x.1*y.1)%P)+P-(x.2*y.2)%P)%P : Nat) : M) = _
    rw [sub_cast _ _ (Nat.mod_lt _ (by decide))]
    simp only [ZMod.natCast_mod, Nat.cast_mul, cMul, decodeC]
  · change ((((((x.1+x.2)*(y.1+y.2))%P+P-(x.1*y.1)%P)%P+P-(x.2*y.2)%P)%P : Nat) : M) = _
    rw [sub_cast _ _ (Nat.mod_lt _ (by decide)),
      sub_cast _ _ (Nat.mod_lt _ (by decide))]
    simp only [ZMod.natCast_mod, Nat.cast_mul, Nat.cast_add, cMul, decodeC]

theorem decode_r (x : WordPair) (hx : CanonicalPair x) :
    decodeC (rWords x) = cR (decodeC x) := by
  apply Prod.ext
  · change (((((x.1+x.1)%P)+P-x.2)%P : Nat) : M) = _
    rw [sub_cast _ _ hx.2]
    simp only [ZMod.natCast_mod, Nat.cast_add, cR, decodeC]
  · change (((x.1+(x.2+x.2)%P)%P : Nat) : M) = _
    simp only [ZMod.natCast_mod, Nat.cast_add, cR, decodeC]

def qMul (x y : Q) : Q :=
  let m0 := cMul x.1 y.1
  let m1 := cMul x.2 y.2
  (cAdd m0 (cR m1),
   cSub (cSub (cMul (cAdd x.1 x.2) (cAdd y.1 y.2)) m0) m1)
def qSquare (x : Q) : Q :=
  (cAdd (cMul x.1 x.1) (cR (cMul x.2 x.2)),
   cAdd (cMul x.1 x.2) (cMul x.1 x.2))

theorem decode_qm_mul (x y : WordPair × WordPair) :
    decodeQ (qmMulWords x y) = qMul (decodeQ x) (decodeQ y) := by
  apply Prod.ext
  · change decodeC (addWords _ _) = _
    rw [decode_add, decode_mul, decode_r _ (mul_canonical _ _), decode_mul]
    rfl
  · change decodeC (subWords (subWords _ _) _) = _
    rw [decode_sub _ _ (mul_canonical _ _), decode_sub _ _ (mul_canonical _ _),
      decode_mul, decode_mul, decode_mul, decode_add, decode_add]
    rfl

theorem decode_qm_square (x : WordPair × WordPair) :
    decodeQ (qmSquareWords x) = qSquare (decodeQ x) := by
  apply Prod.ext
  · change decodeC (addWords _ _) = _
    rw [decode_add, decode_mul, decode_r _ (mul_canonical _ _), decode_mul]
    rfl
  · change decodeC (addWords _ _) = _
    rw [decode_add, decode_mul]
    rfl

#print axioms mul_canonical
#print axioms decode_mul
#print axioms decode_r
#print axioms decode_qm_mul
#print axioms decode_qm_square
#print axioms decode_add
#print axioms sub_cast
#print axioms decode_sub
#print axioms decode_qm_add
#print axioms decode_qm_sub
end AspisV8R17.QM31WordResidues
