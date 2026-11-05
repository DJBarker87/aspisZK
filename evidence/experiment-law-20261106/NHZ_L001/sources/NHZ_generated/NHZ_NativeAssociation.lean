import NHK_TraceBind
import NHS_QueryFailures
import NGP_OracleTransport
set_option autoImplicit false
noncomputable section
namespace AspisR1.NHZ_DRIVER
open Aeneas Aeneas.Std Result CheckpointBytes5Effect
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps

/-- A chronological cut tree, indexed by the actual source code, full Result
and occurrence log. Each callee starts on the preceding callee's returned value.
The caller's state/frame must be in that value. No suffix exists after fail/div.
This is a model composition interface, NOT a producer for native TX1 cuts. -/
inductive Cuts (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest) :
    {A : Type} → Code A → Result A → SdkC_Source.Log → Prop where
 | leaf {A : Type} {code : Code A} {out : Result A} {events : SdkC_Source.Log}
     (trace : NGQ_Cuts.Trace hashv code out events) : Cuts hashv code out events
 | next {A B : Type} {code : Code A} {a : A} {events suffix : SdkC_Source.Log}
     {k : A → Code B} {out : Result B}
     (head : Cuts hashv code (.ok a) events)
     (tail : Cuts hashv (k a) out suffix) :
     Cuts hashv (CheckpointBytes5Effect.bind code k) out (events ++ suffix)
 | fail {A B : Type} {code : Code A} {error : Error} {events : SdkC_Source.Log}
     (head : Cuts hashv code (.fail error) events) (k : A → Code B) :
     Cuts hashv (CheckpointBytes5Effect.bind code k) (.fail error) events
 | div {A B : Type} {code : Code A} {events : SdkC_Source.Log}
     (head : Cuts hashv code .div events) (k : A → Code B) :
     Cuts hashv (CheckpointBytes5Effect.bind code k) .div events

theorem trace {A : Type}
    {hashv : SdkC_Source.Parts → Result SdkC_Source.Digest}
    {code : Code A} {out : Result A} {events : SdkC_Source.Log}
    (cuts : Cuts hashv code out events) : NGQ_Cuts.Trace hashv code out events := by
  induction cuts with
  | leaf t => exact t
  | next _ _ head tail => exact NHK_TraceBind.append head _ _ _ tail
  | fail _ k head =>
    simpa only [List.append_nil] using NHK_TraceBind.append head k _ [] ⟨rfl,rfl⟩
  | div _ k head =>
    simpa only [List.append_nil] using NHK_TraceBind.append head k _ [] ⟨rfl,rfl⟩

/-- Logs append to arbitrary earlier events; neither sorting nor dedup occurs. -/
theorem frame {A : Type}
    {hashv : SdkC_Source.Parts → Result SdkC_Source.Digest}
    {code : Code A} {out : Result A} {events : SdkC_Source.Log}
    (cuts : Cuts hashv code out events) (before : SdkC_Source.Log) :
    SdkC_Source.run hashv code before = (out,before ++ events) :=
  NGQ_Cuts.run (trace cuts) before

/-- Conditional caller theorem. `ordering` is the OPEN exact identification
of the cut-tree code with the deployed TX1 source syntax, not a Result equality.
Physical cut existence/domain/frame installation remains a separate producer. -/
theorem events_from_cuts {A : Type}
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (tx1 cutCode : Code A) (observed : NGP_L181.Observation A)
    (cuts : Cuts hashv cutCode observed.result observed.attempted)
    (ordering : cutCode = tx1) : NGP_L181.NativeAssociation hashv tx1 observed := by
  subst cutCode
  exact NGQ_Cuts.association observed (trace cuts)

theorem prefix_from_cuts {A : Type}
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (sha256 H : Bytes → State) (tx1 cutCode : Code A)
    (observed : NGP_L181.Observation A)
    (cuts : Cuts hashv cutCode observed.result observed.attempted)
    (ordering : cutCode = tx1)
    (p1 : S2W_ExtractionBoundary.P1 sha256 H)
    (syscall : S2W_ExtractionBoundary.RuntimeSyscall hashv sha256) :
    NGP_L181.Prefix_statement H tx1 observed :=
  NGP_OracleTransport.prefix_of_native hashv sha256 H tx1 observed
    (events_from_cuts hashv tx1 cutCode observed cuts ordering) p1 syscall

/-- Install the delivered SAME invocation query packet as a local cut. -/
theorem queries_cut
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (self : AspisR1PublicPreparation.transcript.Transcript Unit)
    (row : U8) (payload : Slice U8)
    (observed : NGP_L181.Observation NGQ_Effects.Reply)
    (cuts : NHK_Invocation.Cuts hashv self row payload observed) :
    Cuts hashv (NGQ_Normalize.normalize
      (NGQ_Effects.code NGQ_TRANSCRIPT.boundaries self row payload))
      observed.result observed.attempted :=
  .leaf (NHK_Invocation.producer cuts)

#print axioms trace
#print axioms frame
#print axioms events_from_cuts
#print axioms prefix_from_cuts
#print axioms queries_cut
end AspisR1.NHZ_DRIVER
