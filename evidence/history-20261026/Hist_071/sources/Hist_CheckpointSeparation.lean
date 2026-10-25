import Hist_AuthDistinct
import Hist_DistinctOuter
import Hist_ValidateCut
import Hist_SecondSnapshot
import Hist_RuntimeEntry
set_option autoImplicit false
noncomputable section
namespace AspisR1.Hist_CheckpointSeparation
open Aeneas Aeneas.Std Result S2W_D189Entry
open AspisR1.AdapterRw.Cuts Hist_Store Hist_RuntimeEntry

theorem authenticated (base : AdapterRw.Ops) (verifier pool : AdapterRw.solana_pubkey.Pubkey)
    (accounts : Slice Account) (lane : U8) (slot : U64)
    (out : AdapterRw.r1_pool_adapter.AuthenticatedAsq8Accounts)
    (success : AdapterRw.r1_pool_adapter.owned.authenticate_asq8_accounts
      (Hist_Authority.install base) verifier accounts pool lane slot = ok (.Ok out)) :
    ∃ forest checkpoint, Slice.index_usize accounts 2#usize = ok forest ∧
      Slice.index_usize accounts 6#usize = ok checkpoint ∧ forest.key ≠ checkpoint.key := by
  obtain ⟨proof,master,forest,selected,registry,entry,checkpoint,_,_,iforest,_,_,_,icp,guard⟩ :=
    Hist_AuthDistinct.distinct_call (Hist_Authority.install base) verifier pool accounts lane slot out success
  have separate := Hist_DistinctOuter.accepted base
    (Array.make 7#usize [proof,master,forest,selected,registry,entry,checkpoint]) guard
    (⟨6,by decide⟩ : Fin 7) (⟨2,by decide⟩ : Fin 7) (by decide)
  change forest.key ≠ checkpoint.key at separate
  exact ⟨forest,checkpoint,iforest,icp,separate⟩

theorem reader (base : AdapterRw.Ops) (program : AdapterRw.solana_pubkey.Pubkey)
    (accounts : Slice Account) (data : Slice U8) (current : core.result.Result U64 PE)
    (success : AdapterRw.r1_pool_adapter.owned.stage2_owned (Hist_Authority.install base)
      program accounts data current = ok (.Ok ())) :
    ∃ forest checkpoint, Slice.index_usize accounts 2#usize = ok forest ∧
      Slice.index_usize accounts 6#usize = ok checkpoint ∧ forest.key ≠ checkpoint.key := by
  obtain ⟨validated,pa,ca,raw,cp,pub,selected,finish,validation,_,_,_,_,_,_,_,_⟩ :=
    S2X.second_fixed_range (Hist_Authority.install base) program accounts data current success
  obtain ⟨pool,lane,slot,out,auth⟩ := Hist_ValidateCut.authenticated
    (Hist_Authority.install base) program accounts data current validated validation
  exact authenticated base program pool accounts lane slot out auth

theorem forest_index (e : Entry) :
    Slice.index_usize (e.second S2W_D189Wrappers.secondSizes) 2#usize = ok (e.snapshot 2 192 192) := rfl

/-- The actual successful reader cannot alias Pool's forest CP2 with the
verifier's CP6 even at the runtime cell level. No assumption of unequal
program ids, distinct keys or a source-layout predicate is needed. -/
theorem distinct_cells (base : AdapterRw.Ops) (program : AdapterRw.solana_pubkey.Pubkey)
    (store : Store) (layout : Layout) (data : Slice U8) (current : core.result.Result U64 PE)
    (success : AdapterRw.r1_pool_adapter.owned.stage2_owned (Hist_Authority.install base)
      program ((load store layout).second S2W_D189Wrappers.secondSizes) data current = ok (.Ok ())) :
    (layout.handles 2).1 ≠ (layout.handles 6).1 := by
  obtain ⟨forest,checkpoint,iforest,icp,separate⟩ := reader base program _ data current success
  have sameForest := Result.ok.inj (iforest.symm.trans (forest_index (load store layout)))
  have sameCheckpoint := Result.ok.inj (icp.symm.trans (Hist_SecondSnapshot.second_index (load store layout)))
  subst forest; subst checkpoint
  intro sameCell
  apply separate
  change (layout.records (layout.handles 2).1).owned.key = (layout.records (layout.handles 6).1).owned.key
  rw [sameCell]

#print axioms authenticated
#print axioms reader
#print axioms forest_index
#print axioms distinct_cells
end AspisR1.Hist_CheckpointSeparation
end
