import NGP_L181
set_option autoImplicit false
noncomputable section
namespace AspisR1.NGP_OracleTransport
open Aeneas Aeneas.Std Result
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open NGP_L181

theorem prefix_of_native {A : Type}
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (sha256 H : Bytes → State) (code : CheckpointBytes5Effect.Code A)
    (observed : Observation A) (native : NativeAssociation hashv code observed)
    (p1 : S2W_ExtractionBoundary.P1 sha256 H)
    (syscall : S2W_ExtractionBoundary.RuntimeSyscall hashv sha256) :
    Prefix_statement H code observed := by
  have same := congrArg Prod.snd native
  dsimp only at same
  obtain ⟨kept,suffix,actual,ideal⟩ := RPx_AttemptPrefix.transport code hashv sha256 H p1 syscall []
  refine ⟨suffix, ?_⟩
  change (eval H (SdkC_Oracle.program code)).1.map Prod.fst =
    RPx_AttemptPrefix.addresses observed.attempted ++ suffix
  rw [same]
  have address : RPx_AttemptPrefix.addresses (SdkC_Source.run hashv code []).2 = kept := by
    simpa only [RPx_AttemptPrefix.addresses,List.map_nil,List.nil_append] using actual
  rw [address]
  exact ideal

theorem exact_of_returns {A : Type}
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (H : Bytes → State) (code : CheckpointBytes5Effect.Code A)
    (observed : Observation A) (native : NativeAssociation hashv code observed)
    (returns : ARR_ReturnCoverage.ReturnsOnly observed.attempted)
    (agrees : ARS_QueryTransport.Agrees H observed.attempted) :
    Exact_statement H code observed := by
  have result := congrArg Prod.fst native
  have log := congrArg Prod.snd native
  dsimp only at result log
  change observed.result = _ ∧ _ ∧ _
  rw [result,log]
  rw [log] at returns agrees
  exact ARS_QueryTransport.exact hashv H code returns agrees

#print axioms prefix_of_native
#print axioms exact_of_returns
end AspisR1.NGP_OracleTransport
