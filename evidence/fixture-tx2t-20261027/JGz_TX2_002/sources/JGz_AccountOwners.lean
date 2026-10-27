import JFv_World
import Hist_Metadata
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGz_AccountOwners
open Aeneas Aeneas.Std Result S2W_D189Entry S2W_D189Wrappers

theorem owner (proofAccount : Slice U8) :
    ((JFv_World.e2 proofAccount).snapshot 1 384 384).owner=CPH_Program.verifier := rfl
#print axioms owner

theorem master_index (proofAccount : Slice U8) :
    Slice.index_usize ((JFv_World.e2 proofAccount).second secondSizes) 1#usize=
      ok ((JFv_World.e2 proofAccount).snapshot 1 384 384) := rfl
#print axioms master_index

/-- Source readonly-owner authentication cannot hold for a different Pool ID.
This rejects the retained account tuple, not all possible fixture tuples. -/
theorem master_rejects (base : AdapterRw.Ops) (proofAccount : Slice U8)
    (pool : AdapterRw.solana_pubkey.Pubkey) (different : pool≠CPH_Program.verifier) :
    AdapterRw.r1_pool_adapter.owned.require_readonly_account (Hist_Authority.install base)
      ((JFv_World.e2 proofAccount).snapshot 1 384 384) pool ≠ ok (.Ok ()) := by
  intro accepted
  have same := (Hist_Metadata.readonly_owner base _ pool accepted).1
  exact different same.symm
#print axioms master_rejects
end AspisR1.JGz_AccountOwners
end
