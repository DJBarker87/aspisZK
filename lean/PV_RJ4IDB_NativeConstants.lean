import PV_RJ4IDB_PowersTotal
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RJ4IDB_NativeConstants
open Aeneas Aeneas.Std Result ProverRwFull ProverRwDictionaryTower
variable [ExternalTypes]
def zero : W := ⟨⟨⟨0#u32,0#u32⟩,⟨0#u32,0#u32⟩⟩,⟨⟨0#u32,0#u32⟩,⟨0#u32,0#u32⟩⟩⟩
def one : W := ⟨⟨⟨1#u32,0#u32⟩,⟨0#u32,0#u32⟩⟩,⟨⟨0#u32,0#u32⟩,⟨0#u32,0#u32⟩⟩⟩

theorem zero_source (ops : ExternalFuns) :
 @aspis_core.field.wide_exact.WideExact.ZERO _ (PV_RJ4IDB_NativePowers.primitives ops) = ok zero := rfl

theorem one_source (ops : ExternalFuns) :
 @ProverRwP6PowersSource.aspis_core.field.wide_exact.WideExact.ONE _
 (PV_RJ4IDB_NativePowers.primitives ops) = ok one := rfl

/-- Actual static specialization size, with the original incoming record
preserved outside op254. No canonicality or success premise is needed. -/
theorem deployed29_total (ops : ExternalFuns) (x : W) :
 ∃ out, (PV_RJ4IDB_NativePowers.installed ops).op254 29#usize x = ok out :=
 PV_RJ4IDB_PowersTotal.complete ops 29#usize x
#print axioms zero_source
#print axioms one_source
#print axioms deployed29_total
end R1Z.PV_RJ4IDB_NativeConstants
