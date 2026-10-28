import R1Z.PV_RDCD_Defaults194
set_option autoImplicit false
namespace R1Z.PV_RDCD_EmptyRaw194
open Aeneas Aeneas.Std Result
/-- Numeric view of the existing Rust usize/Alignment/NonZero/pointer primitive
    representation boundary; no dereference, allocation or write occurs here. -/
def powerOfTwo (a : Usize) : Bool := a.bv.cpop.toNat == 1

def alignmentOf (a : Usize) : Result Usize :=
  if powerOfTwo a then ok a else fail .panic
/-- RawVecInner::new_in(Global,align) constructs only these metadata fields. -/
structure EmptyRaw where
  address : Usize
  cap : Usize
  deriving DecidableEq

def rawNew {World : Type} (a : Usize) (world : World) : Result (EmptyRaw × World) := do
  let align ← alignmentOf a
  -- NonNull::without_provenance(addr.get()) and both transmute conversions
  -- retain the address at the Rust primitive representation boundary.
  ok (⟨align,0#usize⟩,world)

theorem power_four : powerOfTwo 4#usize = true := by
  rcases System.Platform.numBits_eq with h | h <;>
    simp [powerOfTwo,UScalar.ofNat,UScalar.ofNatCore,UScalarTy.numBits,h,BitVec.cpop,BitVec.cpopNatRec]

theorem alignment_valid (a : Usize) (h : powerOfTwo a = true) : alignmentOf a = ok a := by
  simp [alignmentOf,h]

theorem raw_valid {World : Type} (a : Usize) (world : World) (h : powerOfTwo a = true) :
    rawNew a world = ok (⟨a,0#usize⟩,world) := by
  simp [rawNew,alignment_valid a h]
/-- Both concrete native element types have the recorded public alignment4;
    array Default applies the same constructor10 or16 times. -/
theorem raw_four {World : Type} (world : World) :
    rawNew 4#usize world = ok (⟨4#usize,0#usize⟩,world) := raw_valid _ _ power_four

theorem zero_length_view (T : Type) (payload : List T) :
    payload.take 0 = (alloc.vec.Vec.new T).val := rfl

#print axioms power_four
#print axioms alignment_valid
#print axioms raw_valid
#print axioms raw_four
#print axioms zero_length_view
end R1Z.PV_RDCD_EmptyRaw194
