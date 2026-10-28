import R1Z.PV_RunJoin_FixedColumn34
import R1Z.ProverRwDictionaryTower
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_FixedSlice34
open Aeneas Aeneas.Std Result ProverRwFull
open PV_RunJoin_FixedColumn34
variable [ExternalTypes]

def array (values : Slice Q) (length : values.val.length=1024) : Array Q 1024#usize :=
  ⟨values.val,length⟩

theorem as_slice (values : Slice Q) (length : values.val.length=1024) :
    Array.to_slice (array values length) = values := rfl

/-- Complete source result at the exact length checked for G and H1 padding
in the emitted caller. No successful ZERO leaf is assumed. -/
theorem complete (ops : ExternalFuns) (values : Slice Q) (length : values.val.length=1024) :
    @prover.fixed_k_column _ ops values =
      (do let _ ← @aspis_core.field.QM31.ZERO _ ops; .ok (array values length)) := by
  simpa only [as_slice] using
    @PV_RunJoin_FixedColumn34.complete _ ops (array values length)

/-- On the source dictionary with the existing exact ZERO entry installed,
the emitted helper returns the entire original 1024-cell input. Native
allocation, library and dictionary association are separate obligations. -/
theorem installed (ops : ExternalFuns) (values : Slice Q) (length : values.val.length=1024) :
    @prover.fixed_k_column _ (ProverRwDictionaryTower.selected ops) values =
      .ok (array values length) := by
  rw [complete]
  rfl

/-- The original array contents are preserved, with no field normalization
or semantic projection of the QM31 constructor. -/
theorem installed_contents (ops : ExternalFuns) (values : Slice Q) (length : values.val.length=1024) :
    ∃ out, @prover.fixed_k_column _ (ProverRwDictionaryTower.selected ops) values = .ok out ∧
      out.val = values.val := ⟨_,installed ops values length,rfl⟩

#print axioms array
#print axioms as_slice
#print axioms complete
#print axioms installed
#print axioms installed_contents
end R1Z.PV_RunJoin_FixedSlice34
