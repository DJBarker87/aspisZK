import AspisV8R17.UnsignedLiteralSupport

/-! Pinned generated reducer with only #u32 literal macros expanded to U32.ofNat.
The literal support leaf proves the expanded constructor semantics for every
bound proof. This is a focused source projection, not a full R17 caller replay. -/
namespace Aeneas.Std
-- SOURCE Bitwise.lean
instance {ty0 ty1} : HShiftRight (UScalar ty0) (UScalar ty1) (Result (UScalar ty0)) where
  hShiftRight x y := UScalar.shiftRight_UScalar x y
-- END SOURCE
-- SOURCE Bitwise.lean
instance {ty} : HAnd (UScalar ty) (UScalar ty) (UScalar ty) where
  hAnd x y := UScalar.and x y
-- END SOURCE
-- SOURCE Ops/Sub.lean
instance {ty} : HSub (UScalar ty) (UScalar ty) (Result (UScalar ty)) where
  hSub x y := UScalar.sub x y
-- END SOURCE
end Aeneas.Std

namespace V7Tag73CurrentHelpersOpaque
open Aeneas Aeneas.Std Result

-- EXPANDED GENERATED FunsChunk04.lean
@[global_simps, irreducible, rust_const "aspis_core::field::P"]
def aspis_core.field.P : Std.U32 := (U32.ofNat 2147483647)
-- END EXPANDED GENERATED

-- EXPANDED GENERATED FunsChunk04.lean
@[rust_fun "aspis_core::field::reduce_u64"]
def aspis_core.field.reduce_u64 (x : Std.U64) : Result Std.U32 := do
  let i ← lift (UScalar.cast .U64 aspis_core.field.P)
  let i1 ← lift (x &&& i)
  let i2 ← x >>> (U32.ofNat 31)
  let x1 ← i1 + i2
  let i3 ← lift (UScalar.cast .U64 aspis_core.field.P)
  let i4 ← lift (x1 &&& i3)
  let i5 ← x1 >>> (U32.ofNat 31)
  let x2 ← i4 + i5
  let x3 ← lift (UScalar.cast .U32 x2)
  if x3 >= aspis_core.field.P
  then x3 - aspis_core.field.P
  else ok x3
-- END EXPANDED GENERATED
end V7Tag73CurrentHelpersOpaque

namespace AspisV8R17.GeneratedReducerExpanded
open Aeneas.Std V7Tag73CurrentHelpersOpaque UnsignedReducerExecution

theorem generated_reducer_eq (x : U64) :
    aspis_core.field.reduce_u64 x = reduceExecution x := by
  simp only [aspis_core.field.reduce_u64, aspis_core.field.P, reduceExecution,
    foldExecution, mask64, mask32, lift, bind_tc_ok, bind_assoc_eq]
  rfl

theorem generated_reducer_mod (x : U64) :
    ∃ y : U32, aspis_core.field.reduce_u64 x = .ok y ∧
      y.val = x.val % RawReducer.P ∧ y.val < RawReducer.P := by
  rw [generated_reducer_eq]
  exact reduceExecution_mod x

#print axioms generated_reducer_eq
#print axioms generated_reducer_mod
end AspisV8R17.GeneratedReducerExpanded
