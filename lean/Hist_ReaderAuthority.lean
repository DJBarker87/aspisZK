import Hist_Asq8Guards
import Hist_ValidateCut
import Hist_Metadata
set_option autoImplicit false
noncomputable section
namespace AspisR1.Hist_ReaderAuthority
open Aeneas Aeneas.Std Result
open AspisR1.AdapterRw.Cuts

/-- The actual successful TX2 source path authenticates the separate verifier
checkpoint at slot6; no independently successful authentication is supplied. -/
theorem accepted (base : AdapterRw.Ops) (program : AdapterRw.solana_pubkey.Pubkey)
    (accounts : Slice Account) (data : Slice U8) (current : core.result.Result U64 PE)
    (success : AdapterRw.r1_pool_adapter.owned.stage2_owned (Hist_Authority.install base)
      program accounts data current = ok (.Ok ())) :
    ∃ checkpoint, Slice.index_usize accounts 6#usize = ok checkpoint ∧
      checkpoint.owner = program ∧ checkpoint.is_signer = false ∧
      checkpoint.executable = false ∧ checkpoint.is_writable = false := by
  obtain ⟨validated,pa,ca,raw,cp,pub,selected,finish,validation,_,_,_,_,_,_,_,_⟩ :=
    S2X.second_fixed_range (Hist_Authority.install base) program accounts data current success
  obtain ⟨pool,lane,slot,authenticated,auth⟩ := Hist_ValidateCut.authenticated
    (Hist_Authority.install base) program accounts data current validated validation
  obtain ⟨master,forest,selected,checkpoint,_,_,_,index,guard,_,_,_⟩ :=
    Hist_Asq8Guards.guards (Hist_Authority.install base) program pool accounts lane slot authenticated auth
  obtain ⟨signer,executable,writable⟩ := Hist_Metadata.checkpoint_flags
    (Hist_Authority.install base) checkpoint program false guard
  exact ⟨checkpoint,index,Hist_Authority.checkpoint_owner base checkpoint program false guard,
    signer,executable,writable⟩

/-- The Pool forest checkpoint is a separate owner-authenticated account2,
with its own readonly metadata; it is never account6's verifier CP. -/
theorem forest (base : AdapterRw.Ops) (program : AdapterRw.solana_pubkey.Pubkey)
    (accounts : Slice Account) (data : Slice U8) (current : core.result.Result U64 PE)
    (success : AdapterRw.r1_pool_adapter.owned.stage2_owned (Hist_Authority.install base)
      program accounts data current = ok (.Ok ())) :
    ∃ pool checkpoint, Slice.index_usize accounts 2#usize = ok checkpoint ∧
      checkpoint.owner = pool ∧ checkpoint.is_signer = false ∧
      checkpoint.is_writable = false ∧ checkpoint.executable = false := by
  obtain ⟨validated,pa,ca,raw,cp,pub,selected,finish,validation,_,_,_,_,_,_,_,_⟩ :=
    S2X.second_fixed_range (Hist_Authority.install base) program accounts data current success
  obtain ⟨pool,lane,slot,authenticated,auth⟩ := Hist_ValidateCut.authenticated
    (Hist_Authority.install base) program accounts data current validated validation
  obtain ⟨master,forest,selected,checkpoint,_,index,_,_,_,_,guard,_⟩ :=
    Hist_Asq8Guards.guards (Hist_Authority.install base) program pool accounts lane slot authenticated auth
  exact ⟨pool,forest,index,Hist_Metadata.readonly_owner base forest pool guard⟩

#print axioms accepted
#print axioms forest
end AspisR1.Hist_ReaderAuthority
end
