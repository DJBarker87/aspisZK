import PV_B3P_Operations12227
import PV_B3P_RangeFold13227
import PV_B3P_ReconstructNative14227
import PV_B3P_EqualityNative14227
namespace PV_B3P_Native15227
open Aeneas Aeneas.Std PV_B3P_227 PV_B3P_Binding9227 PV_B3P_Binding10227 PV_B3P_Binding11227 PV_B3P_Binding12227 PV_B3P_Binding13227 Result
set_option autoImplicit false

open PV_B3P_Loans14227
/-- Copying a shared array argument for a value read preserves its loan token.
The exact extracted read helper is only an indexed immutable read. -/
def shared_read15 {N : Usize} (loan : Shared14 (Array aspis_core.field.QM31 N)) (index : Usize) :=
  reference_terminal.read227 loan.value index

theorem shared_read_binding15 {N : Usize}
    (loan : Shared14 (Array aspis_core.field.QM31 N)) (index : Usize) :
    shared_read15 loan index = Array.index_usize loan.value index := rfl

theorem shared_read_success15 {N : Usize}
    (loan : Shared14 (Array aspis_core.field.QM31 N)) (index : Usize) (bound : index.val < N.val) :
    ∃ value, shared_read15 loan index = .ok value := by
  rw [shared_read_binding15]
  exact ⟨_,PV_B3P_SelectIndex227.index_value loan.value index bound⟩

theorem shared_read_preserves_identity15 {N : Usize}
    (loan : Shared14 (Array aspis_core.field.QM31 N)) (index : Usize) :
    (do let value ← shared_read15 loan index; .ok (loan.identity,value)) =
      (do let value ← Array.index_usize loan.value index; .ok (loan.identity,value)) := by
  rw [shared_read_binding15]
#print axioms shared_read_binding15
#print axioms shared_read_success15
#print axioms shared_read_preserves_identity15
end PV_B3P_Native15227
