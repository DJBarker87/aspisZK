import PV_THR2_OperatorOriginalRun
import PV_THR2_ChildCallReturned
set_option autoImplicit false
noncomputable section
namespace PV_THR2_OwnInitActualReturnedCases
open Aeneas Aeneas.Std PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine PV_EVHB_OwnerMachine
/-- The installed original carrier stack, with no new value semantics. -/
def carrier (C : Carrier OWNER Data) (b : Bool) :=
  PV_THR2_EntryDynamic.carrier (PV_THR2_ThreadFields.carrier
    (PV_THR2_ScopeLiterals.carrier (PV_THR2_RangeLiterals.carrier C))) b
/-- Exactly a returned case at an actual issued child request. Failed operand
selection does not become an endpoint premise. Each site is named separately. -/
def ReturnedAt {E : Type} (C : Carrier OWNER Data)
    (H : PV_STX2_Native.Request Data → OWNER → Reply OWNER E Data)
    (q : PV_THR2_IntrinsicState.State OWNER E) (nodes : List PV_STX2_SliceSyntax.Node)
    (fn : Data) (args : List Operand) : Prop :=
  ∀ c, q.current.status = .running c →
    PV_THR2_IntrinsicAtContinuation.Ready nodes c →
    ∀ vs t, operands C q.current.world c.frame.activation args c.store = some (vs,t) →
      ∃ v, (H (.child fn t.nextActivation vs) q.current.world).answer = .returned (.ok v)
/-- Exact source composition input to child 7916; no new execution. -/
def before7916 {E : Type} (C : Carrier OWNER Data) (K : Control)
    (fallback : Data → Option PV_STX2_SliceSyntax.Program)
    (H : PV_STX2_Native.Request Data → OWNER → Reply OWNER E Data)
    (q : PV_THR2_IntrinsicState.State OWNER E) :=
    let q0 := q
    let q0 := q
    let q1 := PV_THR2_Source15ClosureAggregate.after C q0
    let q2 := PV_THR2_Source15SpawnEnter.after C q1
    let q3 := PV_THR2_Source166Prologue.after C q2
    q3
/-- Exact source composition input to child 10098; no new execution. -/
def before10098 {E : Type} (C : Carrier OWNER Data) (K : Control)
    (fallback : Data → Option PV_STX2_SliceSyntax.Program)
    (H : PV_STX2_Native.Request Data → OWNER → Reply OWNER E Data)
    (q : PV_THR2_IntrinsicState.State OWNER E) :=
    let q0 := q
    let q0 := q
    let q1 := PV_THR2_Source15ClosureAggregate.after C q0
    let q2 := PV_THR2_Source15SpawnEnter.after C q1
    let q3 := PV_THR2_Source166Prologue.after C q2
    let q4 := PV_THR2_Source166BuilderFull.after C H q3
    let q5 := PV_THR2_Source166Captures.after C q4
    let q6 := PV_THR2_Source166Enter270.after C q5
    let q7 := PV_THR2_Source270Prologue.after C q6
    q7
/-- Exact source composition input to child 12111; no new execution. -/
def before12111 {E : Type} (C : Carrier OWNER Data) (K : Control)
    (fallback : Data → Option PV_STX2_SliceSyntax.Program)
    (H : PV_STX2_Native.Request Data → OWNER → Reply OWNER E Data)
    (q : PV_THR2_IntrinsicState.State OWNER E) :=
    let rootSpawn := PV_THR2_OwnUniformSpawnRun.after C K fallback H q
    let q0 := rootSpawn
    q0
/-- Exact source composition input to child 12199; no new execution. -/
def before12199 {E : Type} (C : Carrier OWNER Data) (K : Control)
    (fallback : Data → Option PV_STX2_SliceSyntax.Program)
    (H : PV_STX2_Native.Request Data → OWNER → Reply OWNER E Data)
    (q : PV_THR2_IntrinsicState.State OWNER E) :=
    let rootSpawn := PV_THR2_OwnUniformSpawnRun.after C K fallback H q
    let q0 := rootSpawn
    let q1 := PV_THR2_Source361Full23.after C H q0
    let q2 := PV_THR2_Source361Chain24To27.after C q1
    q2
/-- Exact source composition input to child 12290; no new execution. -/
def before12290 {E : Type} (C : Carrier OWNER Data) (K : Control)
    (fallback : Data → Option PV_STX2_SliceSyntax.Program)
    (H : PV_STX2_Native.Request Data → OWNER → Reply OWNER E Data)
    (q : PV_THR2_IntrinsicState.State OWNER E) :=
    let rootSpawn := PV_THR2_OwnUniformSpawnRun.after C K fallback H q
    let q0 := rootSpawn
    let q1 := PV_THR2_Source361Full23.after C H q0
    let q2 := PV_THR2_Source361Chain24To27.after C q1
    let q3 := PV_THR2_Source361Full27.after C H q2
    let q4 := PV_THR2_Source361Chain28To34.after C q3
    q4
/-- Exact source composition input to child 12399; no new execution. -/
def before12399 {E : Type} (C : Carrier OWNER Data) (K : Control)
    (fallback : Data → Option PV_STX2_SliceSyntax.Program)
    (H : PV_STX2_Native.Request Data → OWNER → Reply OWNER E Data)
    (q : PV_THR2_IntrinsicState.State OWNER E) :=
    let rootSpawn := PV_THR2_OwnUniformSpawnRun.after C K fallback H q
    let q0 := rootSpawn
    let q1 := PV_THR2_Source361Full23.after C H q0
    let q2 := PV_THR2_Source361Chain24To27.after C q1
    let q3 := PV_THR2_Source361Full27.after C H q2
    let q4 := PV_THR2_Source361Chain28To34.after C q3
    let q5 := PV_THR2_Source361Full34.after C H q4
    let q6 := PV_THR2_Source361Chain35To40.after C q5
    let q7 := PV_THR2_Source361HookBranch.after C q6
    q7
/-- Exact source composition input to child 12509; no new execution. -/
def before12509 {E : Type} (C : Carrier OWNER Data) (K : Control)
    (fallback : Data → Option PV_STX2_SliceSyntax.Program)
    (H : PV_STX2_Native.Request Data → OWNER → Reply OWNER E Data)
    (q : PV_THR2_IntrinsicState.State OWNER E) :=
    let rootSpawn := PV_THR2_OwnUniformSpawnRun.after C K fallback H q
    let q0 := rootSpawn
    let q1 := PV_THR2_Source361Full23.after C H q0
    let q2 := PV_THR2_Source361Chain24To27.after C q1
    let q3 := PV_THR2_Source361Full27.after C H q2
    let q4 := PV_THR2_Source361Chain28To34.after C q3
    let q5 := PV_THR2_Source361Full34.after C H q4
    let q6 := PV_THR2_Source361Chain35To40.after C q5
    let q7 := PV_THR2_Source361HookBranch.after C q6
    let q8 := PV_THR2_Source361HookTrueFull.after C H q7
    let q9 := PV_THR2_Source361HookFalsePrefix.after C q8
    q9
/-- Exact source composition input to child 12668; no new execution. -/
def before12668 {E : Type} (C : Carrier OWNER Data) (K : Control)
    (fallback : Data → Option PV_STX2_SliceSyntax.Program)
    (H : PV_STX2_Native.Request Data → OWNER → Reply OWNER E Data)
    (q : PV_THR2_IntrinsicState.State OWNER E) :=
    let rootSpawn := PV_THR2_OwnUniformSpawnRun.after C K fallback H q
    let q0 := rootSpawn
    let q1 := PV_THR2_Source361Full23.after C H q0
    let q2 := PV_THR2_Source361Chain24To27.after C q1
    let q3 := PV_THR2_Source361Full27.after C H q2
    let q4 := PV_THR2_Source361Chain28To34.after C q3
    let q5 := PV_THR2_Source361Full34.after C H q4
    let q6 := PV_THR2_Source361Chain35To40.after C q5
    let q7 := PV_THR2_Source361HookBranch.after C q6
    let q8 := PV_THR2_Source361HookTrueFull.after C H q7
    let q9 := PV_THR2_Source361HookFalsePrefix.after C q8
    let q10 := PV_THR2_Source361HookFalseFull.after C H q9
    let q11 := PV_THR2_Source361HookTrueSuffix.after C q10
    let q12 := PV_THR2_Source361HookFalseSuffix.after C q11
    let q13 := PV_THR2_Source361Chain41To49.after C q12
    let q14 := PV_THR2_Source361Aggregate49.after C q13
    q14
/-- Exact source composition input to child 12801; no new execution. -/
def before12801 {E : Type} (C : Carrier OWNER Data) (K : Control)
    (fallback : Data → Option PV_STX2_SliceSyntax.Program)
    (H : PV_STX2_Native.Request Data → OWNER → Reply OWNER E Data)
    (q : PV_THR2_IntrinsicState.State OWNER E) :=
    let rootSpawn := PV_THR2_OwnUniformSpawnRun.after C K fallback H q
    let q0 := rootSpawn
    let q1 := PV_THR2_Source361Full23.after C H q0
    let q2 := PV_THR2_Source361Chain24To27.after C q1
    let q3 := PV_THR2_Source361Full27.after C H q2
    let q4 := PV_THR2_Source361Chain28To34.after C q3
    let q5 := PV_THR2_Source361Full34.after C H q4
    let q6 := PV_THR2_Source361Chain35To40.after C q5
    let q7 := PV_THR2_Source361HookBranch.after C q6
    let q8 := PV_THR2_Source361HookTrueFull.after C H q7
    let q9 := PV_THR2_Source361HookFalsePrefix.after C q8
    let q10 := PV_THR2_Source361HookFalseFull.after C H q9
    let q11 := PV_THR2_Source361HookTrueSuffix.after C q10
    let q12 := PV_THR2_Source361HookFalseSuffix.after C q11
    let q13 := PV_THR2_Source361Chain41To49.after C q12
    let q14 := PV_THR2_Source361Aggregate49.after C q13
    let q15 := PV_THR2_Source361Full50.after C H q14
    let q16 := PV_THR2_Source361Chain51To53.after C q15
    let q17 := PV_THR2_Source361Aggregate53.after C q16
    let q18 := PV_THR2_Source361Aggregate54.after C q17
    let q19 := PV_THR2_Source361Chain55To58.after C q18
    q19
/-- Exact source composition input to child 12950; no new execution. -/
def before12950 {E : Type} (C : Carrier OWNER Data) (K : Control)
    (fallback : Data → Option PV_STX2_SliceSyntax.Program)
    (H : PV_STX2_Native.Request Data → OWNER → Reply OWNER E Data)
    (q : PV_THR2_IntrinsicState.State OWNER E) :=
    let rootSpawn := PV_THR2_OwnUniformSpawnRun.after C K fallback H q
    let q0 := rootSpawn
    let q1 := PV_THR2_Source361Full23.after C H q0
    let q2 := PV_THR2_Source361Chain24To27.after C q1
    let q3 := PV_THR2_Source361Full27.after C H q2
    let q4 := PV_THR2_Source361Chain28To34.after C q3
    let q5 := PV_THR2_Source361Full34.after C H q4
    let q6 := PV_THR2_Source361Chain35To40.after C q5
    let q7 := PV_THR2_Source361HookBranch.after C q6
    let q8 := PV_THR2_Source361HookTrueFull.after C H q7
    let q9 := PV_THR2_Source361HookFalsePrefix.after C q8
    let q10 := PV_THR2_Source361HookFalseFull.after C H q9
    let q11 := PV_THR2_Source361HookTrueSuffix.after C q10
    let q12 := PV_THR2_Source361HookFalseSuffix.after C q11
    let q13 := PV_THR2_Source361Chain41To49.after C q12
    let q14 := PV_THR2_Source361Aggregate49.after C q13
    let q15 := PV_THR2_Source361Full50.after C H q14
    let q16 := PV_THR2_Source361Chain51To53.after C q15
    let q17 := PV_THR2_Source361Aggregate53.after C q16
    let q18 := PV_THR2_Source361Aggregate54.after C q17
    let q19 := PV_THR2_Source361Chain55To58.after C q18
    let q20 := PV_THR2_Source361Full58.after C H q19
    let q21 := PV_THR2_Source361Chain59To63.after C q20
    q21
/-- Exact source composition input to child 13123; no new execution. -/
def before13123 {E : Type} (C : Carrier OWNER Data) (K : Control)
    (fallback : Data → Option PV_STX2_SliceSyntax.Program)
    (H : PV_STX2_Native.Request Data → OWNER → Reply OWNER E Data)
    (q : PV_THR2_IntrinsicState.State OWNER E) :=
    let rootSpawn := PV_THR2_OwnUniformSpawnRun.after C K fallback H q
    let q0 := rootSpawn
    let q1 := PV_THR2_Source361Full23.after C H q0
    let q2 := PV_THR2_Source361Chain24To27.after C q1
    let q3 := PV_THR2_Source361Full27.after C H q2
    let q4 := PV_THR2_Source361Chain28To34.after C q3
    let q5 := PV_THR2_Source361Full34.after C H q4
    let q6 := PV_THR2_Source361Chain35To40.after C q5
    let q7 := PV_THR2_Source361HookBranch.after C q6
    let q8 := PV_THR2_Source361HookTrueFull.after C H q7
    let q9 := PV_THR2_Source361HookFalsePrefix.after C q8
    let q10 := PV_THR2_Source361HookFalseFull.after C H q9
    let q11 := PV_THR2_Source361HookTrueSuffix.after C q10
    let q12 := PV_THR2_Source361HookFalseSuffix.after C q11
    let q13 := PV_THR2_Source361Chain41To49.after C q12
    let q14 := PV_THR2_Source361Aggregate49.after C q13
    let q15 := PV_THR2_Source361Full50.after C H q14
    let q16 := PV_THR2_Source361Chain51To53.after C q15
    let q17 := PV_THR2_Source361Aggregate53.after C q16
    let q18 := PV_THR2_Source361Aggregate54.after C q17
    let q19 := PV_THR2_Source361Chain55To58.after C q18
    let q20 := PV_THR2_Source361Full58.after C H q19
    let q21 := PV_THR2_Source361Chain59To63.after C q20
    let q22 := PV_THR2_Source361Full63.after C H q21
    let q23 := PV_THR2_Source361Chain64To70.after C q22
    q23
/-- Exact source composition input to child 13323; no new execution. -/
def before13323 {E : Type} (C : Carrier OWNER Data) (K : Control)
    (fallback : Data → Option PV_STX2_SliceSyntax.Program)
    (H : PV_STX2_Native.Request Data → OWNER → Reply OWNER E Data)
    (q : PV_THR2_IntrinsicState.State OWNER E) :=
    let rootSpawn := PV_THR2_OwnUniformSpawnRun.after C K fallback H q
    let q0 := rootSpawn
    let q1 := PV_THR2_Source361Full23.after C H q0
    let q2 := PV_THR2_Source361Chain24To27.after C q1
    let q3 := PV_THR2_Source361Full27.after C H q2
    let q4 := PV_THR2_Source361Chain28To34.after C q3
    let q5 := PV_THR2_Source361Full34.after C H q4
    let q6 := PV_THR2_Source361Chain35To40.after C q5
    let q7 := PV_THR2_Source361HookBranch.after C q6
    let q8 := PV_THR2_Source361HookTrueFull.after C H q7
    let q9 := PV_THR2_Source361HookFalsePrefix.after C q8
    let q10 := PV_THR2_Source361HookFalseFull.after C H q9
    let q11 := PV_THR2_Source361HookTrueSuffix.after C q10
    let q12 := PV_THR2_Source361HookFalseSuffix.after C q11
    let q13 := PV_THR2_Source361Chain41To49.after C q12
    let q14 := PV_THR2_Source361Aggregate49.after C q13
    let q15 := PV_THR2_Source361Full50.after C H q14
    let q16 := PV_THR2_Source361Chain51To53.after C q15
    let q17 := PV_THR2_Source361Aggregate53.after C q16
    let q18 := PV_THR2_Source361Aggregate54.after C q17
    let q19 := PV_THR2_Source361Chain55To58.after C q18
    let q20 := PV_THR2_Source361Full58.after C H q19
    let q21 := PV_THR2_Source361Chain59To63.after C q20
    let q22 := PV_THR2_Source361Full63.after C H q21
    let q23 := PV_THR2_Source361Chain64To70.after C q22
    let q24 := PV_THR2_Source361Full70.after C H q23
    let q25 := PV_THR2_Source361Chain71To76.after C q24
    let q26 := PV_THR2_Source361Aggregate76.after C q25
    let q27 := PV_THR2_Source361Chain77To81.after C q26
    q27
/-- Exact source composition input to child 13522; no new execution. -/
def before13522 {E : Type} (C : Carrier OWNER Data) (K : Control)
    (fallback : Data → Option PV_STX2_SliceSyntax.Program)
    (H : PV_STX2_Native.Request Data → OWNER → Reply OWNER E Data)
    (q : PV_THR2_IntrinsicState.State OWNER E) :=
    let rootSpawn := PV_THR2_OwnUniformSpawnRun.after C K fallback H q
    let rootMetadata := PV_THR2_OwnUniformMetadataRun.after C K fallback H rootSpawn
    let q0 := rootMetadata
    let q1 := PV_THR2_Source361ScopeSomePrefix.after C q0
    q1
/-- Exact source composition input to child 13713; no new execution. -/
def before13713 {E : Type} (C : Carrier OWNER Data) (K : Control)
    (fallback : Data → Option PV_STX2_SliceSyntax.Program)
    (H : PV_STX2_Native.Request Data → OWNER → Reply OWNER E Data)
    (q : PV_THR2_IntrinsicState.State OWNER E) :=
    let rootSpawn := PV_THR2_OwnUniformSpawnRun.after C K fallback H q
    let rootMetadata := PV_THR2_OwnUniformMetadataRun.after C K fallback H rootSpawn
    let q0 := rootMetadata
    let q1 := PV_THR2_Source361ScopeSomePrefix.after C q0
    let q2 := PV_THR2_Source361ScopeSomeDerefFull.after C H q1
    let q3 := PV_THR2_Source361ScopeSomeReference.after C q2
    q3
/-- Exact source composition input to child 13923; no new execution. -/
def before13923 {E : Type} (C : Carrier OWNER Data) (K : Control)
    (fallback : Data → Option PV_STX2_SliceSyntax.Program)
    (H : PV_STX2_Native.Request Data → OWNER → Reply OWNER E Data)
    (q : PV_THR2_IntrinsicState.State OWNER E) :=
    let rootSpawn := PV_THR2_OwnUniformSpawnRun.after C K fallback H q
    let rootMetadata := PV_THR2_OwnUniformMetadataRun.after C K fallback H rootSpawn
    let rootScope := PV_THR2_OwnUniformScopeRun.after C K fallback H rootMetadata
    let q0 := rootScope
    let q1 := PV_THR2_Source361Chain85To92.after C q0
    q1
/-- Exact source composition input to child 16805; no new execution. -/
def before16805 {E : Type} (C : Carrier OWNER Data) (K : Control)
    (fallback : Data → Option PV_STX2_SliceSyntax.Program)
    (H : PV_STX2_Native.Request Data → OWNER → Reply OWNER E Data)
    (q : PV_THR2_IntrinsicState.State OWNER E) :=
    let rootSpawn := PV_THR2_OwnUniformSpawnRun.after C K fallback H q
    let rootMetadata := PV_THR2_OwnUniformMetadataRun.after C K fallback H rootSpawn
    let rootScope := PV_THR2_OwnUniformScopeRun.after C K fallback H rootMetadata
    let q0 := rootScope
    let q1 := PV_THR2_Source361Chain85To92.after C q0
    let q2 := PV_THR2_BoxPathClosureBoxFull.after C H q1
    let q3 := PV_THR2_Source361Chain93To94.after C q2
    let q4 := PV_THR2_BoxPathEnter443.after C q3
    let q5 := PV_THR2_BoxPath443Chain0To5.after C q4
    q5
/-- Exact source composition input to child 16816; no new execution. -/
def before16816 {E : Type} (C : Carrier OWNER Data) (K : Control)
    (fallback : Data → Option PV_STX2_SliceSyntax.Program)
    (H : PV_STX2_Native.Request Data → OWNER → Reply OWNER E Data)
    (q : PV_THR2_IntrinsicState.State OWNER E) :=
    let rootSpawn := PV_THR2_OwnUniformSpawnRun.after C K fallback H q
    let rootMetadata := PV_THR2_OwnUniformMetadataRun.after C K fallback H rootSpawn
    let rootScope := PV_THR2_OwnUniformScopeRun.after C K fallback H rootMetadata
    let q0 := rootScope
    let q1 := PV_THR2_Source361Chain85To92.after C q0
    let q2 := PV_THR2_BoxPathClosureBoxFull.after C H q1
    let q3 := PV_THR2_Source361Chain93To94.after C q2
    let q4 := PV_THR2_BoxPathEnter443.after C q3
    let q5 := PV_THR2_BoxPath443Chain0To5.after C q4
    let q6 := PV_THR2_BoxPath443NewFull.after C H q5
    let q7 := PV_THR2_BoxPath443Chain6To12.after C q6
    q7
/-- Exact source composition input to child 22550; no new execution. -/
def before22550 {E : Type} (C : Carrier OWNER Data) (K : Control)
    (fallback : Data → Option PV_STX2_SliceSyntax.Program)
    (H : PV_STX2_Native.Request Data → OWNER → Reply OWNER E Data)
    (q : PV_THR2_IntrinsicState.State OWNER E) :=
    let rootSpawn := PV_THR2_OwnUniformSpawnRun.after C K fallback H q
    let rootMetadata := PV_THR2_OwnUniformMetadataRun.after C K fallback H rootSpawn
    let rootScope := PV_THR2_OwnUniformScopeRun.after C K fallback H rootMetadata
    let rootBox := PV_THR2_OwnUniformBoxRun.after C K fallback H rootScope
    let q0 := rootBox
    let q1 := PV_THR2_Source361Chain95To106.after C q0
    let q2 := PV_THR2_BoxPathEnter458.after C q1
    let q3 := PV_THR2_BoxPath458Chain0To4.after C q2
    let q4 := PV_THR2_BoxPath458Aggregate4.after C q3
    let q5 := PV_THR2_BoxPathEnter537.after C q4
    let q6 := PV_THR2_BoxPath537Chain0To4.after C q5
    q6
/-- Actual specialized clone input after the named registration segment. -/
def before14535 {E : Type} (C : Carrier OWNER Data) (K : Control)
    (fallback : Data → Option PV_STX2_SliceSyntax.Program)
    (H : PV_STX2_Native.Request Data → OWNER → Reply OWNER E Data)
    (q : PV_THR2_IntrinsicState.State OWNER E) :=
    let q1 := PV_THR2_OwnUniformSpawnRun.after C K fallback H q
    let q2 := PV_THR2_OwnUniformMetadataRun.after C K fallback H q1
    let q3 := PV_THR2_OwnUniformScopeRun.after C K fallback H q2
    let q4 := PV_THR2_OwnUniformBoxRun.after C K fallback H q3
    let q5 := PV_THR2_OwnUniformReconstructRun.after C K fallback H q4
    PV_THR2_OwnUniformReplyJoin.reframe (PV_THR2_OwnUniformRegistrationFrontierJoin.seed q5)
      (PV_THR2_Source361Chain113To118.after C q5)
/-- The 22 named returned cases on one spawning iteration, per D800/D804.
No ready/read/decoder/endpoint premise. Conditional calls remain individual and guarded by their actual syntax;
no hypothetical request at an unselected arm is constrained.
The next93 case includes Some's discriminant; its item value is arbitrary. -/
structure Cases {E : Type} (C : Carrier OWNER Data) (K : Control) (b : Bool)
    (fallback : Data → Option PV_STX2_SliceSyntax.Program)
    (H : PV_STX2_Native.Request Data → OWNER → Reply OWNER E Data)
    (s : Store Data) (a : Nat) (parents : List Frame)
    (w : OWNER) (es : List E) (stack : List Config) (handles iter next : Data) : Prop where
  returned7894 : (PV_THR2_Source164OwnPrefix.reply H (PV_THR2_Source15Call164.entered s a parents) w).answer = .returned (.ok handles)
  returned3420 : (PV_THR2_Source15RangeTo93.reply H
    (PV_THR2_Source15AfterHandles93.returnedStore s a parents handles)
    (PV_THR2_Source164OwnPrefix.reply H (PV_THR2_Source15Call164.entered s a parents) w).world).answer = .returned (.ok iter)
  returned3447Some :
    (PV_THR2_Source15Continue93Captures.reply H
      (PV_THR2_Source15AfterHandlesCaptures.loopStore
        (PV_THR2_Source15AfterHandles93.returnedStore s a parents handles) a iter) a
      (PV_THR2_Source15RangeTo93.reply H
        (PV_THR2_Source15AfterHandles93.returnedStore s a parents handles)
        (PV_THR2_Source164OwnPrefix.reply H (PV_THR2_Source15Call164.entered s a parents) w).world).world).answer = .returned (.ok next) ∧ K.variant next = some 1
  returned7916 : ReturnedAt (carrier C b) H
    (before7916 (carrier C b) K fallback H
      (PV_THR2_Source15AfterHandlesCaptures.after C K b H s a parents w es stack))
    (PV_THR2_F166.live.body.drop 6)
    PV_THR2_SourceSpawnTable.fn269 []
  returned10098 : ReturnedAt (carrier C b) H
    (before10098 (carrier C b) K fallback H
      (PV_THR2_Source15AfterHandlesCaptures.after C K b H s a parents w es stack))
    (PV_THR2_F270.live.body.drop 27)
    PV_THR2_Source270Table.fn360 PV_THR2_Source270ScopeArcFull.source.2.2.2.1
  returned12111 : ReturnedAt (carrier C b) H
    (before12111 (carrier C b) K fallback H
      (PV_THR2_Source15AfterHandlesCaptures.after C K b H s a parents w es stack))
    (PV_THR2_F361.live.body.drop 23)
    PV_THR2_Source361Children.fn23 PV_THR2_Source361Full23.source.2.2.2.1
  returned12199 : ReturnedAt (carrier C b) H
    (before12199 (carrier C b) K fallback H
      (PV_THR2_Source15AfterHandlesCaptures.after C K b H s a parents w es stack))
    (PV_THR2_F361.live.body.drop 27)
    PV_THR2_Source361Children.fn27 PV_THR2_Source361Full27.source.2.2.2.1
  returned12290 : ReturnedAt (carrier C b) H
    (before12290 (carrier C b) K fallback H
      (PV_THR2_Source15AfterHandlesCaptures.after C K b H s a parents w es stack))
    (PV_THR2_F361.live.body.drop 34)
    PV_THR2_Source361Children.fn34 PV_THR2_Source361Full34.source.2.2.2.1
  returned12399 : ReturnedAt (carrier C b) H
    (before12399 (carrier C b) K fallback H
      (PV_THR2_Source15AfterHandlesCaptures.after C K b H s a parents w es stack))
    ((PV_THR2_F361.block42 ++ PV_THR2_F361.live.body.drop 41))
    PV_THR2_Source361HookChildren.fnTrueFull PV_THR2_Source361HookTrueFull.source.2.2.2.1
  returned12509 : ReturnedAt (carrier C b) H
    (before12509 (carrier C b) K fallback H
      (PV_THR2_Source15AfterHandlesCaptures.after C K b H s a parents w es stack))
    ((PV_THR2_F361.block51.drop 4 ++ PV_THR2_F361.live.body.drop 41))
    PV_THR2_Source361HookChildren.fnFalseFull PV_THR2_Source361HookFalseFull.source.2.2.2.1
  returned12668 : ReturnedAt (carrier C b) H
    (before12668 (carrier C b) K fallback H
      (PV_THR2_Source15AfterHandlesCaptures.after C K b H s a parents w es stack))
    (PV_THR2_F361.live.body.drop 50)
    PV_THR2_Source361PacketChildren.fn50 PV_THR2_Source361Full50.source.2.2.2.1
  returned12801 : ReturnedAt (carrier C b) H
    (before12801 (carrier C b) K fallback H
      (PV_THR2_Source15AfterHandlesCaptures.after C K b H s a parents w es stack))
    (PV_THR2_F361.live.body.drop 58)
    PV_THR2_Source361PacketChildren.fn58 PV_THR2_Source361Full58.source.2.2.2.1
  returned12950 : ReturnedAt (carrier C b) H
    (before12950 (carrier C b) K fallback H
      (PV_THR2_Source15AfterHandlesCaptures.after C K b H s a parents w es stack))
    (PV_THR2_F361.live.body.drop 63)
    PV_THR2_Source361PacketChildren.fn63 PV_THR2_Source361Full63.source.2.2.2.1
  returned13123 : ReturnedAt (carrier C b) H
    (before13123 (carrier C b) K fallback H
      (PV_THR2_Source15AfterHandlesCaptures.after C K b H s a parents w es stack))
    (PV_THR2_F361.live.body.drop 70)
    PV_THR2_Source361PacketChildren.fn70 PV_THR2_Source361Full70.source.2.2.2.1
  returned13323 : ReturnedAt (carrier C b) H
    (before13323 (carrier C b) K fallback H
      (PV_THR2_Source15AfterHandlesCaptures.after C K b H s a parents w es stack))
    (PV_THR2_F361.live.body.drop 81)
    PV_THR2_Source361PacketChildren.fn81 PV_THR2_Source361Full81.source.2.2.2.1
  returned13522 : ReturnedAt (carrier C b) H
    (before13522 (carrier C b) K fallback H
      (PV_THR2_Source15AfterHandlesCaptures.after C K b H s a parents w es stack))
    ((PV_THR2_F361.block113.drop 7 ++ PV_THR2_F361.live.body.drop 85))
    PV_THR2_Source361ScopeChildren.fnSomeDerefFull PV_THR2_Source361ScopeSomeDerefFull.source.2.2.2.1
  returned13713 : ReturnedAt (carrier C b) H
    (before13713 (carrier C b) K fallback H
      (PV_THR2_Source15AfterHandlesCaptures.after C K b H s a parents w es stack))
    ((PV_THR2_F361.block113.drop 10 ++ PV_THR2_F361.live.body.drop 85))
    PV_THR2_Source361ScopeChildren.fnSomeCountFull PV_THR2_Source361ScopeSomeCountFull.source.2.2.2.1
  returned13923 : ReturnedAt (carrier C b) H
    (before13923 (carrier C b) K fallback H
      (PV_THR2_Source15AfterHandlesCaptures.after C K b H s a parents w es stack))
    (PV_THR2_F361.live.body.drop 92)
    PV_THR2_Source361BoxTable.fnClosureBoxFull PV_THR2_BoxPathClosureBoxFull.source.2.2.2.1
  returned16805 : ReturnedAt (carrier C b) H
    (before16805 (carrier C b) K fallback H
      (PV_THR2_Source15AfterHandlesCaptures.after C K b H s a parents w es stack))
    (PV_THR2_F443.live.body.drop 5)
    PV_THR2_Source361BoxTable.fn443NewFull PV_THR2_BoxPath443NewFull.source.2.2.2.1
  returned16816 : ReturnedAt (carrier C b) H
    (before16816 (carrier C b) K fallback H
      (PV_THR2_Source15AfterHandlesCaptures.after C K b H s a parents w es stack))
    (PV_THR2_F443.live.body.drop 12)
    PV_THR2_Source361BoxTable.fn443DerefFull PV_THR2_BoxPath443DerefFull.source.2.2.2.1
  returned22550 : ReturnedAt (carrier C b) H
    (before22550 (carrier C b) K fallback H
      (PV_THR2_Source15AfterHandlesCaptures.after C K b H s a parents w es stack))
    (PV_THR2_F537.live.body.drop 4)
    PV_THR2_BoxFromTable.fnUniqueFull PV_THR2_BoxPathUniqueFull.source.2.2.2.1
  returned14535 : ReturnedAt (carrier C b) H
    (before14535 (carrier C b) K fallback H
      (PV_THR2_Source15AfterHandlesCaptures.after C K b H s a parents w es stack))
    (PV_THR2_F361.live.body.drop 118)
    PV_THR2_Source361InitChildren.fnCloneFull PV_THR2_Source361CloneFull.source.2.2.2.1
#print axioms Cases
end PV_THR2_OwnInitActualReturnedCases
