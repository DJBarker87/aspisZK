import NMT_R2_345Return
set_option autoImplicit false
namespace NMT_R2_345
open RSL NMT_345Observation NMT_R2_Observation

def firstArgs (V : VLib) (C : NMT_R2.TX1_345.S1Lib V) (s : ProofData V C) : NMT_R2.TX1_328.Args V :=
 ⟨C.semanticPublic s.statement,s.publicData,slice s.proofData AFTERSTATE_BYTES PROOF_ACCOUNT_BYTES,
  (s.original.data.getD 1 0).toNat⟩

def stepFirst (V : VLib) (C : NMT_R2.TX1_345.S1Lib V)
 (child : NMT_R2.TX1_328.Args V → Env → Obs (Except ProgramError Bytes))
 (s : ProofData V C) (env : Env) : Obs (Except ProgramError Bytes) :=
 tryObs (child (firstArgs V C s) env) (stepReturn s.checkpointData.length)

/-- The public clause is a CLOSED-validator library lemma, not an own-input
345 hypothesis. Its concrete emitted instance is proved separately. -/
def ValidatedPublic (V : VLib) (C : NMT_R2.TX1_345.S1Lib V) : Prop :=
 ∀ st, C.validateStatement st = true → V.publicDom (C.semanticPublic st)

theorem stepFirst_valid (V : VLib) (P : PreparedNew V) (C : NMT_R2.TX1_345.S1Lib V)
 (library : ValidatedPublic V C)
 (child : NMT_R2.TX1_328.Args V → Env → Obs (Except ProgramError Bytes))
 (packet : NMT_R2.TX1_328.RowSpec_328 V P child) (s : ProofData V C) (env : Env) :
 RS.bind (Spec.call (NMT_R2.TX1_328.Domain V) (NMT_R2.TX1_328.Ref V P) (firstArgs V C s))
  (fun bytes => RS.seq (RS.check (bytes.length != s.checkpointData.length) .invalidAccountData)
   (RS.pure bytes)) env (stepFirst V C child s env) := by
 have domain : NMT_R2.TX1_328.Domain V (firstArgs V C s) :=
  library s.statement s.validated
 exact try_valid _ _ _ _ env ⟨domain,packet _ env domain⟩ (fun bytes => stepReturn_valid _ bytes env)
#print axioms stepFirst_valid
end NMT_R2_345
