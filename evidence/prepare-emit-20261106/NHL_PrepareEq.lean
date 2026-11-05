import NHL_EmittedPrepare
set_option autoImplicit false
noncomputable section
namespace AspisR1.NHL_PrepareEq
open Aeneas Aeneas.Std Result AspisR1CurrentCaller

/-- Fixed source constants make optimized wrapping addition checked-safe. -/
theorem logical_add (ops : Ops) :
 lift (Usize.wrapping_add 13831#usize 928#usize)=
 (13831#usize+928#usize : Result Usize) := by
 have checked := (ConcreteConstants.constants_total ops).2.2.2.2.2.1
 rw [checked]
 change ok (Usize.wrapping_add 13831#usize 928#usize)=ok 14759#usize
 congr 1
 apply UScalar.eq_of_val_eq
 rw [Usize.wrapping_add_val_eq]
 change 14759 % UScalar.size .Usize=14759
 apply Nat.mod_eq_of_lt
 rw [UScalar.size_def]
 scalar_tac

/-- Entire newly emitted prepare, all Rust Result arms and post-scratch,
compared with the adopted current-caller body on its exact source constants.
Opaque callees are identical named operations on both sides. -/
theorem source (ops : Ops) {H : Type} (D : aspis_core.digest.Digest32 H)
 (pub : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
 (proof : Slice U8) (hash : H) (obs : Option (verifier.Phase → Result Unit))
 (g : Array aspis_core.field.wide_exact.WideExact 29#usize) :
 NHL_EmittedPrepare.prepare (ConcreteConstants.withConstants ops) D pub proof hash obs g=
 verifier.candidate.prepare (ConcreteConstants.withConstants ops) D pub proof hash obs g := by
 obtain ⟨offset,y1,inactive,logicalY,logicalS,add,folded,round1⟩ := ConcreteConstants.constants_total ops
 unfold NHL_EmittedPrepare.prepare verifier.candidate.prepare
 simp only [logicalS,logicalY,offset,y1,inactive,bind_tc_ok,logical_add ops,add]
 rfl
#print axioms logical_add
#print axioms source
end AspisR1.NHL_PrepareEq
