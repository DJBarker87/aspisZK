import NMX_R5_Bindings242
set_option autoImplicit false
noncomputable section
namespace NMX_R5_AfterAuth242
open Aeneas Aeneas.Std Result AdapterRw NMS_R2N_Interpreted
abbrev L := LIBB_PoolLib.library
abbrev value := NMS_R2Tail242.validatedValue L id

def model (q : NMS_R2Tail242.Request) (auth : RSL.Authenticated)
 (accounts : List RSL.OwnedAccount) : RSL.RS (RSL.TX2_242.Validated L) :=
 RSL.RS.bind (RSL.RS.ofOption accounts.head? .notEnoughAccountKeys) fun a =>
 RSL.RS.bind a.data fun data =>
 RSL.RS.bind (L.scanProof data) fun scanned =>
 RSL.RS.bind (L.reconstruct q auth scanned.1) fun st =>
 RSL.RS.pure ⟨st,scanned.2⟩

/-- Exact post-authentication source suffix; both library children are fixed
and retain every allocating/error/stop observation at their original inputs. -/
theorem full (q : NMS_R2Tail242.Request) (auth : NMS_R2Tail242.Auth)
 (accounts : Slice r1_pool_adapter.owned.OwnedAccount) :
 Simulates (NMS_R2N_RSLError.reply value)
  (NMS_R2Code242Factor.afterAuth (NMS_R2N_Native242Children.children false) q auth accounts)
  (model q (NMS_R2N_RSLPoolCarriers.authenticated auth) (NMS_R2N_RSLPoolCarriers.accounts accounts)) := by
 rw [NMS_R2AfterAuth242.factor,RSL.Spec.bind_pure]
 unfold model
 simp only [NMS_R2N_RSLPoolCarriers.accounts,List.head?_map]
 cases first : accounts.val.head? with
 | none =>
   simp only [Option.map_none,RSL.RS.ofOption,RSL.RS.bind_throw]
   rw [NMS_R2N_RawTry.normalize]
   change Simulates _ (RSL.Spec.bind (RSL.Spec.pure (core.result.Result.Err solana_program_error.ProgramError.NotEnoughAccountKeys)) _) _
   rw [RSL.Spec.bind_pure]
   exact NMS_R2N_Interpreted.pure _ _
 | some a =>
   simp only [Option.map_some,RSL.RS.ofOption,RSL.RS.bind_pure]
   rw [NMS_R2N_RawTry.normalize]
   change Simulates _ (RSL.Spec.bind (RSL.Spec.pure (core.result.Result.Ok a)) _) _
   rw [RSL.Spec.bind_pure]
   exact NMX_R5_Bindings242.tail q auth a
#print axioms full
end NMX_R5_AfterAuth242
end
