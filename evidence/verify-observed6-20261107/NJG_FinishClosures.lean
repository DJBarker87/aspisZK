import NJG_FromFnCongruence
set_option autoImplicit false
namespace AspisR1.NJG_FinishClosures
open Aeneas Aeneas.Std Result AspisR1PublicPreparation

/-- Release MIR uses wrapping_add for the closure's16+i; the adopted cohort
uses checked addition. They agree on EVERY actual from_fn(10) callback index.
Nothing is claimed for an arbitrary unbounded callback supplied by a dictionary. -/
theorem bounded_add (i : Usize) (bound : i.val<10) :
 16#usize+i=ok (Usize.wrapping_add 16#usize i) := by
 have size : 64≤UScalar.size .Usize := by
  rw [UScalar.size_def,UScalarTy.Usize_numBits_eq]
  rcases System.Platform.numBits_eq with h|h <;> simp [h]
 have small:16+i.val<UScalar.size .Usize:=by omega
 have wrap:(Usize.wrapping_add 16#usize i).val=16+i.val := by
  rw [Usize.wrapping_add_val_eq,show (16#usize).val=16 from rfl,Nat.mod_eq_of_lt small]
 obtain ⟨v,call,value⟩:=WP.spec_imp_exists (UScalar.add_spec (x:=16#usize) (y:=i) (by scalar_tac))
 have same:v=Usize.wrapping_add 16#usize i:=by
  apply UScalar.eq_of_val_eq
  simpa only [wrap,show (16#usize).val=16 from rfl] using value
 simpa only [same] using call

theorem second {H : Type} (D : aspis_core.Digest32 H) (claims : FinishModel.Closure2 H)
 (i : Usize) (bound : i.val<10) :
 NJG_FinishBody.r1_semantic.verify_finish.closure_2.Insts.CoreOpsFunctionFnMutTupleUsizeQM31.call_mut D claims i=
 FinishModel.closureFn2 D claims i := by
 unfold NJG_FinishBody.r1_semantic.verify_finish.closure_2.Insts.CoreOpsFunctionFnMutTupleUsizeQM31.call_mut FinishModel.closureFn2
 rw [bounded_add i bound]
 rfl

/-- The std model calls exactly indices<10, including full mutable closure
state, so the release/cohort wrapping distinction is discharged locally. Native
Std/from_fn interpretation remains its existing caller obligation. -/
theorem second_array {H : Type} (D : aspis_core.Digest32 H) (claims : FinishModel.Closure2 H) :
 OraclePortStdBuilder.fromFn 10#usize
  (NJG_FinishBody.r1_semantic.verify_finish.closure_2.Insts.CoreOpsFunctionFnMutTupleUsizeQM31 D) claims=
 OraclePortStdBuilder.fromFn 10#usize (FinishModel.closureFn5 D) claims := by
 apply NJG_FromFnCongruence.source
 intro state i bound
 apply second D state i
 simpa only [show (10#usize).val=10 from rfl] using bound

#print axioms bounded_add
#print axioms second
#print axioms second_array
end AspisR1.NJG_FinishClosures
