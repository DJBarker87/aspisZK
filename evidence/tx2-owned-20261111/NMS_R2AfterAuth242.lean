import NMS_R2AfterAuthEq242
import NMS_R2PoolSites
set_option autoImplicit false
noncomputable section
namespace NMS_R2AfterAuth242
open Aeneas Aeneas.Std AdapterRw
open NMS_R2Tail242 NMS_R2N_Interpreted
/-- Only the emitted finite suffix is reduced. No decoder, reconstruction,
or full-size buffer term is unfolded by this source factor. -/
theorem factor (devnet : Bool) (q : Request) (auth : Auth)
 (accounts : Slice r1_pool_adapter.owned.OwnedAccount) :
 NMS_R2Code242Factor.afterAuth (NMS_R2N_Native242Children.children devnet) q auth accounts =
 RSL.Spec.bind (RSL.Spec.pure accounts.val.head?) fun first =>
 NMS_R2N_RawTry.literal
  (NMS_R2N_Interpreted.liftResult
   (core.option.Option.ok_or first solana_program_error.ProgramError.NotEnoughAccountKeys))
  (NMS_R2Tail242.raw q auth) :=
 NMS_R2AfterAuthEq242.factor devnet q auth accounts

/-- Canonical continuation after the complete233 call, using the fixed source
scanner/reconstruction images. There are no endpoint or child-success inputs. -/
def model (L : RSL.PoolLib) (request : Request → L.Request)
 (candidate : Candidate → L.Afterstate) (statement : Statement → L.Statement)
 (q : Request) (auth : Auth) (accounts : Slice r1_pool_adapter.owned.OwnedAccount) :
 RSL.RS (RSL.TX2_242.Validated L) :=
 let S := NMS_R2PoolSites.install L request candidate statement
 RSL.RS.bind (RSL.RS.ofOption (NMS_R2N_RSLPoolCarriers.accounts accounts).head? .notEnoughAccountKeys) fun account =>
 RSL.RS.bind account.data fun data =>
 RSL.RS.bind (S.scanProof data) fun scanned =>
 RSL.RS.bind (S.reconstruct (request q) (NMS_R2N_RSLPoolCarriers.authenticated auth) scanned.1) fun st =>
 RSL.RS.pure ⟨st,scanned.2⟩

theorem transport (devnet : Bool) (L : RSL.PoolLib) (request : Request → L.Request)
 (candidate : Candidate → L.Afterstate) (statement : Statement → L.Statement)
 (q : Request) (auth : Auth) (accounts : Slice r1_pool_adapter.owned.OwnedAccount) :
 Simulates (NMS_R2N_RSLError.reply (validatedValue L statement))
  (NMS_R2Code242Factor.afterAuth (NMS_R2N_Native242Children.children devnet) q auth accounts)
  (model L request candidate statement q auth accounts) := by
 rw [factor, RSL.Spec.bind_pure]
 unfold model
 simp only [NMS_R2N_RSLPoolCarriers.accounts,List.head?_map]
 cases first : accounts.val.head? with
 | none =>
   simp only [Option.map_none, RSL.RS.ofOption, RSL.RS.bind_throw]
   rw [NMS_R2N_RawTry.normalize]
   change Simulates _ (RSL.Spec.bind (RSL.Spec.pure (core.result.Result.Err solana_program_error.ProgramError.NotEnoughAccountKeys)) _) _
   rw [RSL.Spec.bind_pure]
   exact NMS_R2N_Interpreted.pure _ _
 | some account =>
   simp only [Option.map_some,RSL.RS.ofOption,RSL.RS.bind_pure]
   rw [NMS_R2N_RawTry.normalize]
   change Simulates _ (RSL.Spec.bind (RSL.Spec.pure (core.result.Result.Ok account)) _) _
   rw [RSL.Spec.bind_pure]
   unfold NMS_R2Tail242.raw
   apply NMS_R2N_RawTry.simulates NMS_R2N_RSLScalars.bytes (validatedValue L statement)
   · exact NMS_R2GetterLink.full account
   · intro data
     apply NMS_R2N_RawTry.simulates (scanValue L candidate) (validatedValue L statement)
     · exact NMS_R2PoolSites.scan_link L candidate data
     · intro scanned
       apply NMS_R2N_RawTry.simulates statement (validatedValue L statement)
       · exact NMS_R2PoolSites.reconstruct_link L request candidate statement q auth scanned.candidate_afterstate
       · intro st
         exact NMS_R2N_Interpreted.pure _ _

#print axioms factor
#print axioms transport
end NMS_R2AfterAuth242
