import NMS_R2GetterLink
import NMS_R2N_Native242Children
import NMS_R2N_RawTry
set_option autoImplicit false
noncomputable section
namespace NMS_R2Tail242
open Aeneas Aeneas.Std AdapterRw
open NMS_R2N_Interpreted
abbrev Statement := aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalStatementV1
abbrev Candidate := aspis_statement.pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1
abbrev Request := aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalRequestV1
abbrev Auth := r1_pool_adapter.AuthenticatedAsq8Accounts
abbrev Scanned := r1_pool_adapter.ScannedAsqaProof
abbrev Validated := r1_pool_adapter.ValidatedAsqa

def scanValue (L : RSL.PoolLib) (candidate : Candidate → L.Afterstate) (s : Scanned) : L.Afterstate × Nat :=
 ⟨candidate s.candidate_afterstate,s.proof_length.val⟩
def validatedValue (L : RSL.PoolLib) (statement : Statement → L.Statement) (v : Validated) : RSL.TX2_242.Validated L :=
 ⟨statement v.statement,v.proof_length.val⟩

/-- The emitted suffix after selecting the proof account. Native buffers stay
symbolic; each child receives exactly its source arguments. -/
def raw (q : Request) (auth : Auth) (account : r1_pool_adapter.owned.OwnedAccount) :=
 NMS_R2N_RawTry.literal (NMS_R2N_GetterMeaning.meaning account) fun data =>
 NMS_R2N_RawTry.literal (NMS_R2N_ScanSites.interpreted data) fun scanned =>
 NMS_R2N_RawTry.literal
  (NMS_R2N_ReconstructSites.meaning q auth scanned.candidate_afterstate) fun statement =>
 RSL.Spec.pure (.Ok (⟨statement,scanned.proof_length⟩ : Validated))

/-- Cross-carrier suffix composition. The two named CLOSED-child links remain
installation obligations, not extra hypotheses of a native row root. -/
theorem transport (L : RSL.PoolLib)
 (request : Request → L.Request) (candidate : Candidate → L.Afterstate)
 (statement : Statement → L.Statement)
 (scan : ∀ data, Simulates (NMS_R2N_RSLError.reply (scanValue L candidate))
   (NMS_R2N_ScanSites.interpreted data) (L.scanProof (NMS_R2N_RSLScalars.bytes data)))
 (reconstruct : ∀ q auth c, Simulates (NMS_R2N_RSLError.reply statement)
   (NMS_R2N_ReconstructSites.meaning q auth c)
   (L.reconstruct (request q) (NMS_R2N_RSLPoolCarriers.authenticated auth) (candidate c)))
 (q : Request) (auth : Auth) (account : r1_pool_adapter.owned.OwnedAccount) :
 Simulates (NMS_R2N_RSLError.reply (validatedValue L statement)) (raw q auth account)
  (RSL.RS.bind (NMS_R2N_RSLPoolCarriers.account account).data fun data =>
   RSL.RS.bind (L.scanProof data) fun scanned =>
   RSL.RS.bind (L.reconstruct (request q) (NMS_R2N_RSLPoolCarriers.authenticated auth) scanned.1) fun st =>
   RSL.RS.pure ⟨st,scanned.2⟩) := by
 unfold raw
 apply NMS_R2N_RawTry.simulates NMS_R2N_RSLScalars.bytes (validatedValue L statement)
 · exact NMS_R2GetterLink.full account
 · intro data
   apply NMS_R2N_RawTry.simulates (scanValue L candidate) (validatedValue L statement)
   · exact scan data
   · intro scanned
     apply NMS_R2N_RawTry.simulates statement (validatedValue L statement)
     · exact reconstruct q auth scanned.candidate_afterstate
     · intro st
       exact NMS_R2N_Interpreted.pure _ _
#print axioms transport
end NMS_R2Tail242
