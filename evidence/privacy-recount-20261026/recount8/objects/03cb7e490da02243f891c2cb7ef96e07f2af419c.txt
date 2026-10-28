import R1Z.ProverRw18ContextCompression
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverRw18ContextTotal
open Aeneas Aeneas.Std Result ProverRwFull
open ProverRw18InlineContext
variable [ExternalTypes]

theorem total (ops : ExternalFuns) (tag : U32) (values : Slice U32) (lambda : Q) :
    ∃ final, @ProverRw18ContextCompression.compress _ (PV_CurrentScaleInstall.selected ops)
      tag values lambda=ok final := by
  rw [ProverRw18ContextCompression.combined]
  exact PV_RW_CombinedCompression.total ops tag values lambda

theorem arity16 (ops : ExternalFuns) (tag : U32) (values : Array U32 16#usize) (lambda : Q) :
    @ProverRw18ContextCompression.compress _ (PV_CurrentScaleInstall.selected ops)
      tag (Array.to_slice values) lambda=PV_RW_CompressClosed.owned tag (Array.to_slice values) lambda :=
  ProverRw18ContextCompression.owned ops tag (Array.to_slice values) lambda

-- There are no success or data-equality hypotheses. This applies to any pair
-- of fixture tuples; the native fixture-to-tuple association is recorded
-- separately, rather than hidden in the theorem's parameters.
theorem paired_total (ops : ExternalFuns) (tag0 tag1 : U32)
    (values0 values1 : Array U32 16#usize) (lambda0 lambda1 : Q) :
    (∃ final, @ProverRw18ContextCompression.compress _ (PV_CurrentScaleInstall.selected ops)
      tag0 (Array.to_slice values0) lambda0=ok final) ∧
    (∃ final, @ProverRw18ContextCompression.compress _ (PV_CurrentScaleInstall.selected ops)
      tag1 (Array.to_slice values1) lambda1=ok final) :=
  ⟨total ops tag0 (Array.to_slice values0) lambda0,total ops tag1 (Array.to_slice values1) lambda1⟩

#print axioms total
#print axioms arity16
#print axioms paired_total
end R1Z.ProverRw18ContextTotal
