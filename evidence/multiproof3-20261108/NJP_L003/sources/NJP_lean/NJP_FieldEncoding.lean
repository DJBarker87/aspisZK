import NJE_RoundTrace

set_option autoImplicit false
noncomputable section
namespace NJP_FieldEncoding
open Aeneas Aeneas.Std Result
abbrev K := NJA_Matrix.K

def word (x : K) : U32 := NJE_Residue.word x.val

theorem value (x : K) : (word x).val=x.val := by
 rw [word,NJE_Residue.value]
 exact Nat.mod_eq_of_lt (ZMod.val_lt x)

theorem canonical (x : K) : (word x).val<2147483647 := NJE_Residue.canonical _

theorem decoded (x : K) : ((word x).val:K)=x := by
 rw [value]
 exact ZMod.natCast_zmod_val x

theorem faithful (x y : U32) (hx : x.val<2147483647) (hy : y.val<2147483647)
    (same : (x.val:K)=(y.val:K)) : x=y := by
 have values := congrArg ZMod.val same
 simp only [ZMod.val_natCast, Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt hy] at values
 exact UScalar.eq_of_val_eq values

theorem unique (x : U32) (z : K) (hx : x.val<2147483647) (same : (x.val:K)=z) :
    x=word z := faithful x (word z) hx (canonical z) (same.trans (decoded z).symm)

#print value
#print axioms value
#print canonical
#print axioms canonical
#print decoded
#print axioms decoded
#print faithful
#print axioms faithful
#print unique
#print axioms unique
end NJP_FieldEncoding
end
