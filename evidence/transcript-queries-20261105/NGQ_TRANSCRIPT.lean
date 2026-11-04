import NGQ_Cuts
set_option autoImplicit false
noncomputable section
namespace AspisR1.NGQ_TRANSCRIPT
open Aeneas Aeneas.Std Result
open AspisR1PublicPreparation
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep

def positions : Result NGQ_Effects.Reply → Option (List U32)
 | .ok (.Ok q,_) => some q.val
 | _ => none

/-- Composes local native edges into the exact NGP_L181 interface and the
SAME-boundary full model Result. The producer of trace remains explicit until
all native cuts, sampler association and frames have been admitted. -/
theorem actual_queries_of_cuts
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (B : QueriesModel.Boundaries) (self : transcript.Transcript Unit)
    (row : U8) (payload : Slice U8) (observed : NGP_L181.Observation NGQ_Effects.Reply)
    (trace : NGQ_Cuts.Trace hashv (NGQ_Effects.code B self row payload)
      observed.result observed.attempted) :
    NGP_L181.NativeAssociation hashv (NGQ_Effects.code B self row payload) observed ∧
    observed.result=QueriesModel.queries B (NGQ_Effects.dictionary hashv) self row payload ∧
    positions observed.result=positions (QueriesModel.queries B (NGQ_Effects.dictionary hashv) self row payload) ∧
    observed.attempted=(SdkC_Source.run hashv (NGQ_Effects.code B self row payload) []).2 := by
  have association := NGQ_Cuts.association observed trace
  have result := congrArg Prod.fst association
  have events := congrArg Prod.snd association
  dsimp only at result events
  have same := result.trans (NGQ_Effects.model_result hashv B self row payload)
  exact ⟨association,same,congrArg positions same,events⟩

/-- Existing partial-runtime policy, with the failed attempt retained. -/
theorem prefix_of_cuts
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest) (sha256 H : Bytes → State)
    (B : QueriesModel.Boundaries) (self : transcript.Transcript Unit)
    (row : U8) (payload : Slice U8) (observed : NGP_L181.Observation NGQ_Effects.Reply)
    (trace : NGQ_Cuts.Trace hashv (NGQ_Effects.code B self row payload)
      observed.result observed.attempted)
    (p1 : S2W_ExtractionBoundary.P1 sha256 H)
    (syscall : S2W_ExtractionBoundary.RuntimeSyscall hashv sha256) :
    NGP_L181.Prefix_statement H (NGQ_Effects.code B self row payload) observed :=
  NGP_OracleTransport.prefix_of_native hashv sha256 H _ observed
    (NGQ_Cuts.association observed trace) p1 syscall

theorem exact_of_cuts
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest) (H : Bytes → State)
    (B : QueriesModel.Boundaries) (self : transcript.Transcript Unit)
    (row : U8) (payload : Slice U8) (observed : NGP_L181.Observation NGQ_Effects.Reply)
    (trace : NGQ_Cuts.Trace hashv (NGQ_Effects.code B self row payload)
      observed.result observed.attempted)
    (returns : ARR_ReturnCoverage.ReturnsOnly observed.attempted)
    (agrees : ARS_QueryTransport.Agrees H observed.attempted) :
    NGP_L181.Exact_statement H (NGQ_Effects.code B self row payload) observed :=
  NGP_OracleTransport.exact_of_returns hashv H _ observed
    (NGQ_Cuts.association observed trace) returns agrees
#print axioms actual_queries_of_cuts
#print axioms prefix_of_cuts
#print axioms exact_of_cuts
end AspisR1.NGQ_TRANSCRIPT
end
