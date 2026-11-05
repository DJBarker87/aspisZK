import NIA_ConstructorTrace
set_option autoImplicit false
noncomputable section
namespace AspisR1.NIA_ScalarFailures
open Aeneas Aeneas.Std Result CheckpointBytes5Effect AspisR1PublicPreparation
open NIA_ScalarEffects

/-- These are Aeneas partial outcomes, not invented Rust verifier::Error arms. -/
inductive Stop where
 | fail (error : Error)
 | div

def Stop.result {A : Type} : Stop → Result A
 | .fail e => .fail e
 | .div => .div

/-- Primitive unsuccessful edge at one of the actual three reads. Earlier
replies are fixed and later calls are absent. Row overflow records no syscall. -/
inductive BlockStop (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
 (before : transcript.Transcript Unit) (row : U8) (payload : Slice U8) :
 Stop → SdkC_Source.Log → Prop where
 | tag (stop : Stop) (edge : (160#u8+row : Result U8)=stop.result) :
     BlockStop hashv before row payload stop []
 | absorb (stop : Stop) (tag : U8) (tagCall : (160#u8+row : Result U8)=.ok tag)
     (edge : hashv (NGT_NBA_Transcript.absorbParts before.state tag payload)=stop.result) :
     BlockStop hashv before row payload stop
       [⟨NGT_NBA_Transcript.absorbParts before.state tag payload,stop.result⟩]
 | read (stop : Stop) (tag : U8) (absorbed : SdkC_Source.Digest)
     (tagCall : (160#u8+row : Result U8)=.ok tag)
     (first : hashv (NGT_NBA_Transcript.absorbParts before.state tag payload)=.ok absorbed)
     (edge : hashv (NGT_NBA_Transcript.readParts absorbed 1#u8)=stop.result) :
     BlockStop hashv before row payload stop
       [⟨NGT_NBA_Transcript.absorbParts before.state tag payload,.ok absorbed⟩,
        ⟨NGT_NBA_Transcript.readParts absorbed 1#u8,stop.result⟩]
 | advance (stop : Stop) (tag : U8) (absorbed value : SdkC_Source.Digest)
     (tagCall : (160#u8+row : Result U8)=.ok tag)
     (first : hashv (NGT_NBA_Transcript.absorbParts before.state tag payload)=.ok absorbed)
     (second : hashv (NGT_NBA_Transcript.readParts absorbed 1#u8)=.ok value)
     (edge : hashv (NGT_NBA_Transcript.readParts absorbed 2#u8)=stop.result) :
     BlockStop hashv before row payload stop
       [⟨NGT_NBA_Transcript.absorbParts before.state tag payload,.ok absorbed⟩,
        ⟨NGT_NBA_Transcript.readParts absorbed 1#u8,.ok value⟩,
        ⟨NGT_NBA_Transcript.readParts absorbed 2#u8,stop.result⟩]

variable {hashv : SdkC_Source.Parts → Result SdkC_Source.Digest}
 {before : transcript.Transcript Unit} {row : U8} {payload : Slice U8}
 {stop : Stop} {events : SdkC_Source.Log}

theorem block_trace (packet : BlockStop hashv before row payload stop events) :
 NGQ_Cuts.Trace hashv (NHZ_DRIVER.scalarBlockCode before row payload) stop.result events := by
 cases packet with
 | tag edge => cases stop with
   | fail e => exact .stepFail _ _ e edge
   | div => exact .stepDiv _ _ edge
 | absorb tag tagCall edge =>
   apply NGQ_Cuts.Trace.stepOk _ _ tag tagCall
   cases stop with
   | fail e => exact .readFail _ _ e edge
   | div => exact .readDiv _ _ edge
 | read tag absorbed tagCall first edge =>
   apply NGQ_Cuts.Trace.stepOk _ _ tag tagCall
   apply NGQ_Cuts.Trace.readOk _ _ absorbed first
   cases stop with
   | fail e => exact .readFail _ _ e edge
   | div => exact .readDiv _ _ edge
 | advance tag absorbed value tagCall first second edge =>
   apply NGQ_Cuts.Trace.stepOk _ _ tag tagCall
   apply NGQ_Cuts.Trace.readOk _ _ absorbed first
   apply NGQ_Cuts.Trace.readOk _ _ value second
   cases stop with
   | fail e => exact .readFail _ _ e edge
   | div => exact .readDiv _ _ edge

theorem block_result (packet : BlockStop hashv before row payload stop events) :
 transcript.Transcript.block (NGQ_Effects.dictionary hashv) before row payload=stop.result := by
 rw [←block_evaluate, NIA_ConstructorTrace.evaluate_run hashv _ []]
 exact congrArg Prod.fst (NGQ_Cuts.run (block_trace packet) [])

theorem scalar_result (B : PreparedModel.Boundaries) (mode : Bool)
 (packet : BlockStop hashv before row payload stop events) :
 PreparedModel.scalar B (NGQ_Effects.dictionary hashv) before row payload mode=stop.result := by
 unfold PreparedModel.scalar
 rw [block_result packet]
 cases stop <;> rfl

theorem scalarK_result (B : PreparedModel.Boundaries)
 (packet : BlockStop hashv before row payload stop events) :
 PreparedModel.scalar_k B (NGQ_Effects.dictionary hashv) before row payload=stop.result := by
 unfold PreparedModel.scalar_k
 rw [block_result packet]
 cases stop <;> rfl

theorem scalar_trace (B : PreparedModel.Boundaries) (mode : Bool)
 (packet : BlockStop hashv before row payload stop events) :
 NGQ_Cuts.Trace hashv (scalarCode B before row payload mode) stop.result events := by
 unfold scalarCode
 cases stop <;>
   simpa only [List.append_nil,Stop.result] using
     NHK_TraceBind.append (block_trace packet) _ _ [] ⟨rfl,rfl⟩

theorem scalarK_trace (B : PreparedModel.Boundaries)
 (packet : BlockStop hashv before row payload stop events) :
 NGQ_Cuts.Trace hashv (scalarKCode B before row payload) stop.result events := by
 unfold scalarKCode
 cases stop <;>
   simpa only [List.append_nil,Stop.result] using
     NHK_TraceBind.append (block_trace packet) _ _ [] ⟨rfl,rfl⟩

/-- Frame-chain extension for the SAME stopped invocation, arbitrary prior log,
all payload lengths and both scalar modes. Existing NGT ok laws are unchanged. -/
theorem frame (B : PreparedModel.Boundaries) (mode : Bool)
 (packet : BlockStop hashv before row payload stop events) (prior : SdkC_Source.Log) :
 SdkC_Source.run hashv (scalarCode B before row payload mode) prior=(stop.result,prior++events) ∧
 SdkC_Source.run hashv (scalarKCode B before row payload) prior=(stop.result,prior++events) :=
 ⟨NGQ_Cuts.run (scalar_trace B mode packet) prior,NGQ_Cuts.run (scalarK_trace B packet) prior⟩

#print axioms block_trace
#print axioms block_result
#print axioms scalar_result
#print axioms scalarK_result
#print axioms scalar_trace
#print axioms scalarK_trace
#print axioms frame
end AspisR1.NIA_ScalarFailures
