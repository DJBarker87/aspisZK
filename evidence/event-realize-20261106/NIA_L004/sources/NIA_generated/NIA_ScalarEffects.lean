import NHZ_ScalarEvents
set_option autoImplicit false
noncomputable section
namespace AspisR1.NIA_ScalarEffects
open Aeneas Aeneas.Std Result CheckpointBytes5Effect AspisR1PublicPreparation

def evaluate (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
 {A : Type} : Code A → Result A
 | .done a => .ok a
 | .step r k => do let b ← r; evaluate hashv (k b)
 | .read parts k => do let d ← hashv parts; evaluate hashv (k d)

theorem evaluate_bind (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
 {A B : Type} (code : Code A) (k : A → Code B) :
 evaluate hashv (CheckpointBytes5Effect.bind code k)=
 (do let a ← evaluate hashv code; evaluate hashv (k a)) := by
 induction code with
 | done a => rfl
 | step r next ih => cases r <;> simp only [CheckpointBytes5Effect.bind,evaluate,bind_tc_ok,bind_tc_fail,bind_tc_div,ih]
 | read parts next ih =>
   cases edge : hashv parts <;> simp only [CheckpointBytes5Effect.bind,evaluate,edge,bind_tc_ok,bind_tc_fail,bind_tc_div,ih]

theorem evaluate_lift (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
 {A : Type} (r : Result A) : evaluate hashv (liftResult r)=r := by
 cases r <;> rfl

/-- Construct a complete local trace from each primitive reply of the explicit
syntax. This does not identify that syntax with a physical native execution. -/
theorem complete (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
 {A : Type} (code : Code A) :
 ∃ events, NGQ_Cuts.Trace hashv code (evaluate hashv code) events := by
 induction code with
 | done a => exact ⟨[],.done a⟩
 | step r k ih =>
   cases r with
   | ok b => obtain ⟨events,tail⟩ := ih b; exact ⟨events,.stepOk _ _ b rfl _ _ tail⟩
   | fail e => exact ⟨[],.stepFail _ _ e rfl⟩
   | div => exact ⟨[],.stepDiv _ _ rfl⟩
 | read parts k ih =>
   cases edge : hashv parts with
   | ok d =>
     obtain ⟨events,tail⟩ := ih d
     exact ⟨⟨parts,.ok d⟩::events,.readOk _ _ d edge _ _ (by simpa only [evaluate,edge,bind_tc_ok] using tail)⟩
   | fail e => exact ⟨[⟨parts,.fail e⟩],by simpa only [evaluate,edge,bind_tc_fail] using NGQ_Cuts.Trace.readFail parts k e edge⟩
   | div => exact ⟨[⟨parts,.div⟩],by simpa only [evaluate,edge,bind_tc_div] using NGQ_Cuts.Trace.readDiv parts k edge⟩

def scalarCode (B : PreparedModel.Boundaries) (before : transcript.Transcript Unit)
 (row : U8) (payload : Slice U8) (mode : Bool) :
 Code (aspis_core.field.WideExact × transcript.Transcript Unit) :=
 CheckpointBytes5Effect.bind (NHZ_DRIVER.scalarBlockCode before row payload) fun (block,after) =>
 .step (if mode then B.gamma block else B.ordinary block) fun out =>
 .step (lift (UScalar.cast .Usize row)) fun i =>
 .step (AspisR1PublicPreparation.trace.value 4#u16 i out) fun _ => .done (out,after)

def scalarKCode (B : PreparedModel.Boundaries) (before : transcript.Transcript Unit)
 (row : U8) (payload : Slice U8) :
 Code (aspis_core.field.QM31 × transcript.Transcript Unit) :=
 CheckpointBytes5Effect.bind (NHZ_DRIVER.scalarBlockCode before row payload) fun (block,after) =>
 .step (AspisR1PublicPreparation.sampler.qm31_sample block) fun out =>
 .step (lift (UScalar.cast .Usize row)) fun i =>
 .step (B.fromQm out) fun embedded =>
 .step (AspisR1PublicPreparation.trace.value 4#u16 i embedded) fun _ => .done (out,after)

theorem block_evaluate (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
 (before : transcript.Transcript Unit) (row : U8) (payload : Slice U8) :
 evaluate hashv (NHZ_DRIVER.scalarBlockCode before row payload)=
 transcript.Transcript.block (NGQ_Effects.dictionary hashv) before row payload := by
 simp only [NHZ_DRIVER.scalarBlockCode,evaluate,transcript.Transcript.block,
   transcript.Transcript.absorb,NGT_NBA_Transcript.absorbParts,NGT_NBA_Transcript.readParts,
   NGQ_Effects.dictionary,lift,bind_tc_ok,bind_assoc_eq]

theorem scalar_evaluate (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
 (B : PreparedModel.Boundaries) (before : transcript.Transcript Unit)
 (row : U8) (payload : Slice U8) (mode : Bool) :
 evaluate hashv (scalarCode B before row payload mode)=
 PreparedModel.scalar B (NGQ_Effects.dictionary hashv) before row payload mode := by
 simp only [scalarCode,evaluate_bind,evaluate_lift,block_evaluate,PreparedModel.scalar,evaluate]

theorem scalarK_evaluate (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
 (B : PreparedModel.Boundaries) (before : transcript.Transcript Unit)
 (row : U8) (payload : Slice U8) :
 evaluate hashv (scalarKCode B before row payload)=
 PreparedModel.scalar_k B (NGQ_Effects.dictionary hashv) before row payload := by
 simp only [scalarKCode,evaluate_bind,evaluate_lift,block_evaluate,PreparedModel.scalar_k,evaluate]

#print axioms evaluate_bind
#print axioms evaluate_lift
#print axioms complete
#print axioms block_evaluate
#print axioms scalar_evaluate
#print axioms scalarK_evaluate
end AspisR1.NIA_ScalarEffects
