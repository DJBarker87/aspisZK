import NCK_AuthenticationCuts
set_option autoImplicit false
noncomputable section
namespace AspisR1.NCK_AuthenticationDomains
open Aeneas Aeneas.Std Result
open AdapterRw.Cuts
open _root_.AdapterRw.r1_pool_adapter.owned

/-- The exact accepted model call proves its seven-key, owner, privilege and
checkpoint-length domains. Only the primitive comparison/size laws remain;
no metadata domain or successful guard is separately assumed. -/
theorem source (ops : _root_.AdapterRw.Ops)
    (program pool : _root_.AdapterRw.solana_pubkey.Pubkey) (accounts : Slice Account)
    (lane : U8) (slot : U64)
    (authenticated : _root_.AdapterRw.r1_pool_adapter.AuthenticatedAsq8Accounts)
    (comparison : NCK_DistinctInner.Comparison ops)
    (size : ops.op12 .S2 = ok 1768#usize)
    (success : authenticate_asq8_accounts ops program accounts pool lane slot = ok (.Ok authenticated)) :
    ∃ proof master poolCheckpoint laneAccount registry entry checkpoint,
      Slice.len accounts = 7#usize ∧
      Slice.index_usize accounts 0#usize = ok proof ∧
      Slice.index_usize accounts 1#usize = ok master ∧
      Slice.index_usize accounts 2#usize = ok poolCheckpoint ∧
      Slice.index_usize accounts 3#usize = ok laneAccount ∧
      Slice.index_usize accounts 4#usize = ok registry ∧
      Slice.index_usize accounts 5#usize = ok entry ∧
      Slice.index_usize accounts 6#usize = ok checkpoint ∧
      (proof.is_signer = false ∧ proof.is_writable = false ∧ proof.executable = false) ∧
      (checkpoint.owner = program ∧ checkpoint.is_signer = false ∧ checkpoint.executable = false ∧
        checkpoint.is_writable = false ∧ OwnedAccount.data_len ops checkpoint = ok (.Ok 1768#usize)) ∧
      (master.owner = pool ∧ master.is_signer = false ∧ master.is_writable = false ∧ master.executable = false) ∧
      (poolCheckpoint.owner = pool ∧ poolCheckpoint.is_signer = false ∧ poolCheckpoint.is_writable = false ∧ poolCheckpoint.executable = false) ∧
      (laneAccount.owner = pool ∧ laneAccount.is_signer = false ∧ laneAccount.is_writable = false ∧ laneAccount.executable = false) ∧
      NCK_DistinctOuter.Remaining
        (Array.make 7#usize [proof,master,poolCheckpoint,laneAccount,registry,entry,checkpoint]) 0 := by
  obtain ⟨p,m,pc,l,r,e,cp,length,i0,i1,i2,i3,i4,i5,i6,hp,hcp,hm,hpc,hl,hd⟩ :=
    NCK_AuthenticationCuts.guards ops program pool accounts lane slot authenticated success
  have proofFlags := (NCK_Readonly.buffer_accepts p.is_signer p.is_writable p.executable).mp hp
  exact ⟨p,m,pc,l,r,e,cp,length,i0,i1,i2,i3,i4,i5,i6,proofFlags,
    NCK_Owners.checkpoint ops cp program false comparison size hcp,
    NCK_Owners.readonly ops m pool comparison hm,
    NCK_Owners.readonly ops pc pool comparison hpc,
    NCK_Owners.readonly ops l pool comparison hl,
    NCK_Distinct.accepted ops _ comparison hd⟩
#print axioms source
end AspisR1.NCK_AuthenticationDomains
end
