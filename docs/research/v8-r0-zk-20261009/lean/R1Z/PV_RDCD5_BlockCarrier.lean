import R1Z.PV_AL_BlockCodec
set_option autoImplicit false
namespace R1Z.PV_RDCD5_BlockCarrier
open Aeneas Aeneas.Std PV_CBL_GenericArrayPower

/-- A typed storage tree has one byte interpretation. Re-encoding that exact
interpretation recovers the tree, including its zero-length base arrays. This
is a carrier theorem; native repr(C)/transparent layout stays at V370. -/
theorem encode_flatten (k : Nat) (v : Storage U8 k) :
    PV_AL_BlockCodec.encode k (flatten k v) = v := by
  induction k with
  | zero =>
    rcases v with ⟨left,right,data⟩
    have hl : left = Array.make 0#usize [] := by
      apply Subtype.ext
      exact List.eq_nil_of_length_eq_zero left.property
    have hr : right = Array.make 0#usize [] := by
      apply Subtype.ext
      exact List.eq_nil_of_length_eq_zero right.property
    subst left
    subst right
    rfl
  | succ k ih =>
    rcases v with ⟨left,right,marker⟩
    cases marker
    simp only [flatten,PV_CBL_GenericArrayFlatten.even,
      PV_AL_BlockCodec.encode,← length k left,List.take_left,List.drop_left,ih]

/-- The byte projection loses no information in the concrete U64 carrier. -/
theorem flatten_injective (k : Nat) : Function.Injective (flatten (T := U8) k) := by
  intro a b h
  have e := congrArg (PV_AL_BlockCodec.encode k) h
  rwa [encode_flatten,encode_flatten] at e

#print axioms encode_flatten
#print axioms flatten_injective
end R1Z.PV_RDCD5_BlockCarrier
