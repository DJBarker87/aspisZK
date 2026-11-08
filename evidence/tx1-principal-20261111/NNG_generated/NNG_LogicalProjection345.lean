import NNG_ProjectAccounts345
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNG_LogicalProjection345
open RSL NNG_Phases345
abbrev V := LIB_Instances.VL
abbrev C := LIB_Instances.C

def parent (s : Parent) : Parent :=
 ⟨NNG_ProjectAccounts345.args s.original,NNG_ProjectAccounts345.account s.proofAccount,
 NNG_ProjectAccounts345.account s.publicAccount,NNG_ProjectAccounts345.account s.checkpointAccount⟩
def checkpoint (s : CheckpointData) : CheckpointData := ⟨parent s.toParent,NNG_Cut345.cut s.checkpointData⟩
def publicData (s : PublicData) : PublicData := ⟨checkpoint s.toCheckpointData,NNG_Cut345.cut s.publicData⟩
def decoded (s : Decoded V C) : Decoded V C :=
 ⟨publicData s.toPublicData,s.statement,(NNG_Cut345.decode s.publicData).trans s.decoded⟩
def validated (s : Validated V C) : Validated V C := ⟨decoded s.toDecoded,s.validated⟩
def candidate (s : Candidate V C) : Candidate V C := ⟨validated s.toValidated,s.candidate⟩
def proofData (s : ProofData V C) : ProofData V C := ⟨candidate s.toCandidate,NNG_Cut345.cut s.proofData⟩

theorem public_fixed (s : Decoded V C) : NNG_Cut345.cut s.publicData=s.publicData := by
 apply NNG_Cut345.fixed
 have size := NNG_P1880Discharge.decoder V rfl s.publicData s.statement s.decoded
 rw [size]
 change 1880≤Aeneas.Std.Usize.max
 scalar_tac
#print axioms public_fixed

theorem firstArgs (s : ProofData V C) (proof : s.proofData.length≤Aeneas.Std.Usize.max) :
 NNG_Phases345.firstArgs V C (proofData s)=NNG_Phases345.firstArgs V C s := by
 change (⟨C.semanticPublic s.statement,NNG_Cut345.cut s.publicData,
  slice (NNG_Cut345.cut s.proofData) AFTERSTATE_BYTES PROOF_ACCOUNT_BYTES,
  (s.original.data.getD 1 0).toNat⟩ : TX1_328.Args V)=_
 rw [public_fixed s.toDecoded,NNG_Cut345.fixed s.proofData proof]
 rfl
#print axioms firstArgs
end AspisR1.NNG_LogicalProjection345
