import NCK_DistinctInner
import NCK_OwnedMeta
import NCK_CheckpointMeta
set_option autoImplicit false
noncomputable section
namespace AspisR1.NCK_Owners
open Aeneas Aeneas.Std Result
open _root_.AdapterRw.r1_pool_adapter _root_.AdapterRw.r1_pool_adapter.owned
open NCK_DistinctInner
attribute [local instance] Classical.propDecidable

theorem ne_exact (ops : _root_.AdapterRw.Ops) (x y : _root_.AdapterRw.solana_pubkey.Pubkey)
    (comparison : Comparison ops) :
    core.cmp.impls.PartialEqShared.ne
      (_root_.AdapterRw.solana_pubkey.Pubkey.Insts.CoreCmpPartialEqPubkey ops) x y =
      ok (decide (x ≠ y)) := by
  simp only [Comparison] at comparison
  simp [core.cmp.impls.PartialEqShared.ne,
    _root_.AdapterRw.solana_pubkey.Pubkey.Insts.CoreCmpPartialEqPubkey,
    core.cmp.PartialEq.ne.default, comparison]

/-- Owner and privilege domains are derived at the accepted readonly guard. -/
theorem readonly (ops : _root_.AdapterRw.Ops) (a : OwnedAccount)
    (owner : _root_.AdapterRw.solana_pubkey.Pubkey) (comparison : Comparison ops)
    (success : require_readonly_account ops a owner = ok (.Ok ())) :
    a.owner = owner ∧ a.is_signer = false ∧ a.is_writable = false ∧ a.executable = false := by
  rw [NCK_OwnedMeta.account_call, NCK_Readonly.account_exact ops a.owner owner
    (decide (a.owner ≠ owner)) a.is_signer a.is_writable a.executable
    (ne_exact ops a.owner owner comparison)] at success
  by_cases own : a.owner = owner <;>
    cases hs : a.is_signer <;> cases hw : a.is_writable <;> cases he : a.executable <;>
    simp_all

/-- The verifier checkpoint is owned by the exact caller program, with the
same deferred length reply, not only by an arbitrary successful comparator. -/
theorem checkpoint (ops : _root_.AdapterRw.Ops) (a : OwnedAccount)
    (program : _root_.AdapterRw.solana_pubkey.Pubkey) (writable : Bool)
    (comparison : Comparison ops) (size : ops.op12 .S2 = ok 1768#usize)
    (success : require_verifier_checkpoint ops a program writable = ok (.Ok ())) :
    a.owner = program ∧ a.is_signer = false ∧ a.executable = false ∧
    a.is_writable = writable ∧ OwnedAccount.data_len ops a = ok (.Ok 1768#usize) := by
  have checkpointFacts := NCK_CheckpointMeta.accepted_domain ops a program writable size success
  have owner : a.owner = program := by
    unfold require_verifier_checkpoint at success
    simp only [OwnedAccount.impl.owner, bind_tc_ok, ne_exact ops a.owner program comparison] at success
    by_contra different
    simp [different] at success
  exact ⟨owner,checkpointFacts⟩
#print axioms ne_exact
#print axioms readonly
#print axioms checkpoint
end AspisR1.NCK_Owners
end
