import R1Z.ProverRwEffectNonzero
set_option autoImplicit false
namespace R1Z.ProverRwEntropyByteOr
open Aeneas Aeneas.Std Result ProverRwFull

theorem or_zero_iff (x y : U8) : x ||| y = 0#u8 ↔ x = 0#u8 ∧ y = 0#u8 := by
  constructor
  · intro h
    have hb := congrArg UScalar.bv h
    change x.bv ||| y.bv = 0#8 at hb
    have hz := BitVec.or_eq_zero_iff.mp hb
    exact ⟨(U8.eq_equiv_bv_eq _ _).mpr hz.1,(U8.eq_equiv_bv_eq _ _).mpr hz.2⟩
  · rintro ⟨rfl,rfl⟩
    rfl

def chain (bytes : List U8) : Nat → Nat → U8 → U8
  | _,0,combined => combined
  | index,fuel+1,combined =>
    chain bytes (index+1) fuel (combined ||| bytes[index]?.getD 0#u8)

theorem chain_zero_iff (bytes : List U8) (index fuel : Nat) (combined : U8) :
    chain bytes index fuel combined = 0#u8 ↔
      combined = 0#u8 ∧ ∀ j, index ≤ j → j < index+fuel → bytes[j]?.getD 0#u8 = 0#u8 := by
  induction fuel generalizing index combined with
  | zero => simp only [chain,Nat.add_zero]; constructor
            · intro h; exact ⟨h,fun j lo hi => by omega⟩
            · exact And.left
  | succ fuel ih =>
    rw [chain,ih,or_zero_iff]
    constructor
    · rintro ⟨⟨hc,head⟩,tail⟩
      refine ⟨hc,?_⟩
      intro j lo hi
      by_cases same : j = index
      · simpa only [same] using head
      · exact tail j (by omega) (by omega)
    · rintro ⟨hc,all⟩
      exact ⟨⟨hc,all index (by omega) (by omega)⟩,
        fun j lo hi => all j (by omega) (by omega)⟩

#print axioms or_zero_iff
#print axioms chain_zero_iff
end R1Z.ProverRwEntropyByteOr
