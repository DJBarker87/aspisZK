import PoolS2_MasterCuts
set_option autoImplicit false
namespace AspisR1.PoolS2_MasterFacts
open Aeneas Aeneas.Std Result PoolS2_PdaSource PoolS2_MasterRead PoolS2_PdaSeeds

theorem accepted (decode : Decode) (pda : Ops) (program : Key) (account : Account)
    (writable : Bool) (master : Master)
    (h : run decode pda program account writable = ok (.Ok master)) :
    account.owner = program ∧ account.executable = false ∧ account.is_writable = writable ∧
    account.is_signer = false ∧ ∃ bytes : alloc.vec.Vec U8,
      account.bytes = .Ok bytes ∧ decode bytes.deref = ok (.Ok master) ∧
      pda.create (masterCreate master.identity.asset_mint master.bump) program = ok (.Ok account.key) ∧
      master.identity.pool = account.key := by
  obtain ⟨metadata,signer,bytes,read,decoded,matched,identity⟩ :=
    PoolS2_MasterCuts.accepted decode pda program account writable master h
  have admitted := (Hiq_PoolGuards.account_iff account program writable).mp metadata
  exact ⟨admitted.1,admitted.2.1,admitted.2.2,signer,bytes,read,decoded,
    PoolS2_PdaMaster.accepted pda program account.key master matched,identity⟩

#print axioms accepted
end AspisR1.PoolS2_MasterFacts
