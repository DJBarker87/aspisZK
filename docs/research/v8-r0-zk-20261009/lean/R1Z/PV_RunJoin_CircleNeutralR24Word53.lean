import R1Z.PV_RunJoin_CircleNeutralR24Leaf53
import R1Z.PV_RunJoin_CircleNeutralResidue53
set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow
namespace R1Z.PV_RunJoin_CircleNeutralR24Word53
open PV_RunJoin_CircleNeutralCast53

def word (n : Nat) : U64 := ⟨BitVec.ofNat 64 n⟩

theorem value (n : Nat) (h : n<18446744073709551616) : (word n).val=n := Nat.mod_eq_of_lt h

theorem add (a b : Nat) : core.num.U64.wrapping_add (word a) (word b) = word (a+b) := by
  change (⟨BitVec.ofNat 64 a+BitVec.ofNat 64 b⟩ : U64) = word (a+b)
  rw [BitVec.ofNat_add_ofNat]
  rfl

theorem sub (a b : Nat) (hb : b<18446744073709551616) (hle : b≤a) :
    core.num.U64.wrapping_sub (word a) (word b) = word (a-b) := by
  change (⟨BitVec.ofNat 64 a-BitVec.ofNat 64 b⟩ : U64) = word (a-b)
  rw [BitVec.ofNat_sub_ofNat_of_le a b hb hle]
  rfl

theorem mul (a b : Nat) (ha : a<18446744073709551616) (hb : b<18446744073709551616)
    (hab : a*b<18446744073709551616) : word a*word b=ok (word (a*b)) := by
  rw [PV_RunJoin_CircleNeutralChecked64_53.mul _ _ (by rw [value a ha,value b hb];exact hab)]
  apply congrArg ok
  apply UScalar.eq_of_val_eq
  rw [PV_RunJoin_CircleNeutralWord53.mul64]
  · rw [value a ha,value b hb,value (a*b) hab]
  · rw [value a ha,value b hb];exact hab

theorem widen (a : U32) : UScalar.cast .U64 a = word a.val := by
  apply UScalar.eq_of_val_eq
  rw [up_val,value]
  have h := a.hBounds
  change a.val<4294967296 at h
  omega

theorem fold (n : Nat) (hn : n<18446744073709551616) :
    PV_RunJoin_CircleNeutralFold53.fold (word n) = word (AspisV8R19.PartialProduct.foldOnce n) := by
  have hf : AspisV8R19.PartialProduct.foldOnce n < 18446744073709551616 := by
    have h := PV_RunJoin_CircleNeutralFold53.fold_bound (word n)
    rw [PV_RunJoin_CircleNeutralFold53.fold_val,value n hn] at h
    change n%2147483648+n/2147483648 < 18446744073709551616
    omega
  apply UScalar.eq_of_val_eq
  rw [PV_RunJoin_CircleNeutralFold53.fold_val,value n hn,value _ hf]
  rfl

#print axioms word
#print axioms value
#print axioms add
#print axioms sub
#print axioms mul
#print axioms widen
#print axioms fold
end R1Z.PV_RunJoin_CircleNeutralR24Word53
