import JGz_AuthenticationObstruction
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGz_DefaultPool
open Aeneas Aeneas.Std Result
/-- Literal fallback in r1_pool_adapter.rs:80-82, default ELF built with the
Pool-program environment override unset. This is not a devnet ID claim. -/
def value : AdapterRw.solana_pubkey.Pubkey := Array.repeat 32#usize 65#u8

theorem different : value≠CPH_Program.verifier := by
  intro same
  have head := congrArg (fun key : AdapterRw.solana_pubkey.Pubkey=>key.val[0]?) same
  change some (65#u8)=some (95#u8) at head
  exact (by decide : (65#u8)≠95#u8) (Option.some.inj head)
#print axioms different

theorem rejects (base : AdapterRw.Ops) (proofAccount : Slice U8) (lane : U8) (slot : U64)
    (out : AdapterRw.r1_pool_adapter.AuthenticatedAsq8Accounts) :
    AdapterRw.r1_pool_adapter.owned.authenticate_asq8_accounts (Hist_Authority.install base)
      CPH_Program.verifier ((JFv_World.e2 proofAccount).second S2W_D189Wrappers.secondSizes)
      value lane slot ≠ ok (.Ok out) :=
  JGz_AuthenticationObstruction.source base proofAccount value lane slot out different
#print axioms rejects
end AspisR1.JGz_DefaultPool
end
