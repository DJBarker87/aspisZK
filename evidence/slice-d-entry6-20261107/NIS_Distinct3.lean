import NHJ_DistinctPacket
set_option autoImplicit false
noncomputable section
namespace NIS_Distinct3
open Aeneas Aeneas.Std Result
abbrev A := NGL_DistinctStep.Account
attribute [local instance] Classical.propDecidable

def array (a b c : A) : Array A 3#usize := ⟨[a,b,c],by rfl⟩

/-- Only three comparisons are reduced; no large finite universe or recurrence. -/
theorem specification (a b c : A) : NGL_DistinctInduction.reference (array a b c)=
    ok (if a.key=b.key ∨ a.key=c.key ∨ b.key=c.key then
      core.result.Result.Err AdapterRw.solana_program_error.ProgramError.InvalidArgument else .Ok ()) := by
  have w0 : Usize.wrapping_add 0#usize 1#usize=1#usize := by
    apply UScalar.eq_of_val_eq
    exact NFQ_ZeroPrimitives.wrap_add 0#usize 1#usize (by change 0+1≤4096; omega)
  have w1 : Usize.wrapping_add 1#usize 1#usize=2#usize := by
    apply UScalar.eq_of_val_eq
    exact NFQ_ZeroPrimitives.wrap_add 1#usize 1#usize (by change 1+1≤4096; omega)
  have w2 : Usize.wrapping_add 2#usize 1#usize=3#usize := by
    apply UScalar.eq_of_val_eq
    exact NFQ_ZeroPrimitives.wrap_add 2#usize 1#usize (by change 2+1≤4096; omega)
  by_cases ab : a.key=b.key <;> by_cases ac : a.key=c.key <;> by_cases bc : b.key=c.key
  all_goals simp_all [NGL_DistinctInduction.reference,NGL_DistinctInduction.outer,
    NGL_DistinctInduction.inner,NGL_DistinctInduction.keyAt,array,w0,w1,w2,ab,ac,bc]

theorem source (ops : AdapterRw.Ops) (a b c : A) :
    AdapterRw.r1_pool_adapter.owned.require_distinct_accounts (NGL_ReadonlyModel.install ops)
      (array a b c)=ok (if a.key=b.key ∨ a.key=c.key ∨ b.key=c.key then
        core.result.Result.Err AdapterRw.solana_program_error.ProgramError.InvalidArgument else .Ok ()) := by
  rw [NHJ_DistinctPacket.three,specification]

#print axioms specification
#print axioms source
end NIS_Distinct3
