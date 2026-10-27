import JFv_World
import Hist_Metadata
set_option autoImplicit false
noncomputable section
namespace AspisR1.JHc_Ownership
open Aeneas Aeneas.Std Result S2W_D189Entry S2W_D189Wrappers

/-- The first wrapper's checkpoint has the required verifier owner. TX1's
readonly proof/public guards do not require Pool ownership. -/
theorem checkpoint_owner (proofAccount : Slice U8) :
    ((JFv_World.e1 proofAccount).snapshot 2 1768 1768).owner=CPH_Program.verifier := rfl
#print axioms checkpoint_owner

theorem flags (proofAccount : Slice U8) :
    ((JFv_World.e1 proofAccount).snapshot 0 58295 58295).is_signer=false ∧
    ((JFv_World.e1 proofAccount).snapshot 0 58295 58295).is_writable=false ∧
    ((JFv_World.e1 proofAccount).snapshot 0 58295 58295).executable=false ∧
    ((JFv_World.e1 proofAccount).snapshot 1 1880 1880).is_signer=false ∧
    ((JFv_World.e1 proofAccount).snapshot 1 1880 1880).is_writable=false ∧
    ((JFv_World.e1 proofAccount).snapshot 1 1880 1880).executable=false ∧
    ((JFv_World.e1 proofAccount).snapshot 2 1768 1768).is_signer=false ∧
    ((JFv_World.e1 proofAccount).snapshot 2 1768 1768).is_writable=true ∧
    ((JFv_World.e1 proofAccount).snapshot 2 1768 1768).executable=false :=
  ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩
#print axioms flags

theorem checkpoint_index (proofAccount : Slice U8) :
    Slice.index_usize (JFv_World.e1 proofAccount).first 2#usize=
      ok ((JFv_World.e1 proofAccount).snapshot 2 1768 1768) := rfl
#print axioms checkpoint_index
theorem readonly_guards (proofAccount : Slice U8) :
    AdapterRw.r1_pool_adapter.owned.require_readonly_buffer
      ((JFv_World.e1 proofAccount).snapshot 0 58295 58295)=ok (.Ok ()) ∧
    AdapterRw.r1_pool_adapter.owned.require_readonly_buffer
      ((JFv_World.e1 proofAccount).snapshot 1 1880 1880)=ok (.Ok ()) := ⟨rfl,rfl⟩
#print axioms readonly_guards
end AspisR1.JHc_Ownership
end
