import NHK_Invocation
set_option autoImplicit false
noncomputable section
namespace AspisR1.NGP_TRANSCRIPT
open Aeneas Aeneas.Std Result AspisR1PublicPreparation
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep

/-- Native packet transport in exactly NGP_L181's interface. The cut packet is
assembled from SAME-invocation local certificates; no model Trace or whole
queries Result/log equality is supplied as a hypothesis. Caller-domain bounds
retain the precise domain of the physical absorb certificate. -/
theorem actual_queries
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (self : transcript.Transcript Unit) (row : U8) (payload : Slice U8)
    (observed : NGP_L181.Observation NGQ_Effects.Reply)
    (_domain : NHK_Invocation.Domain row payload)
    (cuts : NHK_Invocation.Cuts hashv self row payload observed) :
    NGP_L181.NativeAssociation hashv
      (NGQ_Effects.code NGQ_TRANSCRIPT.boundaries self row payload) observed :=
  (NGQ_TRANSCRIPT.actual_queries hashv self row payload observed (NHK_Invocation.producer cuts)).1

theorem cohort
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (self : transcript.Transcript Unit) (row : U8) (payload : Slice U8)
    (observed : NGP_L181.Observation NGQ_Effects.Reply)
    (cuts : NHK_Invocation.Cuts hashv self row payload observed) :
    observed.result = QueriesModel.queries NGQ_TRANSCRIPT.boundaries
      (NGQ_Effects.dictionary hashv) self row payload :=
  (NGQ_TRANSCRIPT.actual_queries hashv self row payload observed (NHK_Invocation.producer cuts)).2.1

/-- Failed/diverging syscalls retain their attempted prefix; no totality is
assumed and the omitted suffix remains in the ideal experiment. -/
theorem prefix
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (sha256 H : Bytes → State)
    (self : transcript.Transcript Unit) (row : U8) (payload : Slice U8)
    (observed : NGP_L181.Observation NGQ_Effects.Reply)
    (domain : NHK_Invocation.Domain row payload)
    (cuts : NHK_Invocation.Cuts hashv self row payload observed)
    (p1 : S2W_ExtractionBoundary.P1 sha256 H)
    (syscall : S2W_ExtractionBoundary.RuntimeSyscall hashv sha256) :
    NGP_L181.Prefix_statement H (NGQ_Effects.code NGQ_TRANSCRIPT.boundaries self row payload) observed :=
  NGP_OracleTransport.prefix_of_native hashv sha256 H _ observed
    (actual_queries hashv self row payload observed domain cuts) p1 syscall

theorem exact
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (H : Bytes → State)
    (self : transcript.Transcript Unit) (row : U8) (payload : Slice U8)
    (observed : NGP_L181.Observation NGQ_Effects.Reply)
    (domain : NHK_Invocation.Domain row payload)
    (cuts : NHK_Invocation.Cuts hashv self row payload observed)
    (returns : ARR_ReturnCoverage.ReturnsOnly observed.attempted)
    (agrees : ARS_QueryTransport.Agrees H observed.attempted) :
    NGP_L181.Exact_statement H (NGQ_Effects.code NGQ_TRANSCRIPT.boundaries self row payload) observed :=
  NGP_OracleTransport.exact_of_returns hashv H _ observed
    (actual_queries hashv self row payload observed domain cuts) returns agrees

#print axioms actual_queries
#print axioms cohort
#print axioms prefix
#print axioms exact
end AspisR1.NGP_TRANSCRIPT
end
