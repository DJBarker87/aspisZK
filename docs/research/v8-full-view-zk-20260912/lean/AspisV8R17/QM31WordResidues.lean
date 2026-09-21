import AspisV8R17.QM31WordFormulas
import Mathlib.Data.ZMod.Basic

/-! Coordinatewise residue interface for the retained explicit tower.
This leaf does not instantiate its quadratic-algebra operations or fields. -/
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

#print axioms decode_add
#print axioms sub_cast
#print axioms decode_sub
#print axioms decode_qm_add
#print axioms decode_qm_sub
end AspisV8R17.QM31WordResidues
