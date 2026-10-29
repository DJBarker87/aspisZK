import NDN_Reference15.Funs
import AdapterRwModel
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace NDN_RequestTagFinding
open AdapterRw.aspis_statement.pool_v1

def zeroTagHeader : Array U8 8#usize :=
 Array.make 8#usize [65#u8,83#u8,81#u8,56#u8,1#u8,0#u8,1#u8,0#u8]

theorem extracted_accepts_zero :
 NDN_Reference15.header_gate zeroTagHeader 320#usize=ok 0#u8 := rfl

theorem source_rejects_zero :
 pair_forest_terminal.transition_kind 0#u8=ok (.Err .InvalidTransitionKind) := rfl

theorem source_accepts_one :
 pair_forest_terminal.transition_kind 1#u8=ok (.Ok .PrivateTransfer) := rfl

theorem source_accepts_two :
 pair_forest_terminal.transition_kind 2#u8=ok (.Ok .Withdrawal) := rfl

#print axioms extracted_accepts_zero
#print axioms source_rejects_zero
#print axioms source_accepts_one
#print axioms source_accepts_two
end NDN_RequestTagFinding
