import PV_FN_THREAD_JoinedPrefix
set_option autoImplicit false
noncomputable section
namespace PV_FN_THREAD_f361Prefix
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine PV_EVHB_OwnerMachine
/-- f361's own entry, independent of F0 and every lower saved caller. -/
def entry {E : Type} (s : Store Data) (a : Nat) (parents : List Frame)
    (w : OWNER) (es : List E) (stack : List Config) : PV_THR2_IntrinsicState.State OWNER E :=
  ⟨⟨.running ⟨{activation := a,remaining := PV_THR2_F361.live.body},parents,s⟩,w,es⟩,stack⟩
def steps {E : Type} (B : Carrier OWNER Data) (K : Control)
    (fallback : Data → Option PV_STX2_SliceSyntax.Program)
    (H : PV_STX2_Native.Request Data → OWNER → Reply OWNER E Data)
    (q : PV_THR2_IntrinsicState.State OWNER E) : Nat :=
  let q1 := PV_THR2_Source361Prologue.after B q
  let q2 := PV_THR2_Source361FirstAggregate.after B q1
  PV_THR2_Source361Prologue.steps B q + (PV_THR2_Source361FirstAggregate.steps B q1 +
    PV_THR2_JoinedCertRegionMetadataPrefix.steps B K fallback H q2)
def after {E : Type} (B : Carrier OWNER Data) (K : Control)
    (fallback : Data → Option PV_STX2_SliceSyntax.Program)
    (H : PV_STX2_Native.Request Data → OWNER → Reply OWNER E Data)
    (q : PV_THR2_IntrinsicState.State OWNER E) : PV_THR2_IntrinsicState.State OWNER E :=
  PV_THR2_JoinedCertRegionMetadataPrefix.after B K fallback H
    (PV_THR2_Source361FirstAggregate.after B (PV_THR2_Source361Prologue.after B q))
/-- Existing segments and the complete retained metadata prefix, BY NAME. -/
theorem source {E : Type} (B : Carrier OWNER Data) (K : Control)
    (fallback : Data → Option PV_STX2_SliceSyntax.Program)
    (H : PV_STX2_Native.Request Data → OWNER → Reply OWNER E Data)
    (q : PV_THR2_IntrinsicState.State OWNER E) :
    PV_THR2_IntrinsicState.advance B K (PV_FN_THREAD_JoinedPrefix.retained fallback) H
      (steps B K fallback H q) q = after B K fallback H q := by
  unfold steps after
  dsimp only
  rw [PV_THR2_IntrinsicComposition.advance_add,PV_THR2_Source361Prologue.run,
    PV_THR2_IntrinsicComposition.advance_add,PV_THR2_Source361FirstAggregate.run]
  exact PV_THR2_JoinedCertRegionMetadataPrefix.source B K fallback H _
/-- Existing shape certificates are composed once, with no source replay. -/
theorem certificate {E : Type} (B : Carrier OWNER Data) (K : Control)
    (fallback : Data → Option PV_STX2_SliceSyntax.Program)
    (H : PV_STX2_Native.Request Data → OWNER → Reply OWNER E Data)
    (q : PV_THR2_IntrinsicState.State OWNER E) :
    PV_THR2_JoinedCertDispatchTrace.Certificate B K (PV_FN_THREAD_JoinedPrefix.retained fallback) H
      (steps B K fallback H q) q := by
  unfold steps
  apply PV_THR2_JoinedCertDispatchTrace.append B K _ H _ _ q _
    (PV_THR2_Source361Prologue.run B K _ H q)
    (PV_THR2_JoinedCertRegionFrontierCertificates.Source361Prologue B K _ H q)
  apply PV_THR2_JoinedCertDispatchTrace.append B K _ H _ _ _ _
    (PV_THR2_Source361FirstAggregate.run B K _ H _)
    (PV_THR2_JoinedCertRegionOneFrontiers.Source361FirstAggregate B K _ H _)
  exact PV_THR2_JoinedCertRegionMetadataPrefix.packet B K fallback H _
/-- Joined resolver from f361 entry through the actual pre12801 boundary.
The124/126 bodies are selected throughout; neither body is summarized here.
Every earlier native full reply, missing operand and branch is retained.
This prefix is not f361's complete-return contract or the OwnInit milestone. -/
theorem run {E : Type} (B : Carrier OWNER Data) (K : Control)
    (fallback : Data → Option PV_STX2_SliceSyntax.Program)
    (H : PV_STX2_Native.Request Data → OWNER → Reply OWNER E Data)
    (q : PV_THR2_IntrinsicState.State OWNER E) :
    PV_THR2_IntrinsicState.advance B K (PV_THR2_PacketJoinedTable.table fallback) H
      (steps B K fallback H q) q = after B K fallback H q :=
  (PV_FN_THREAD_JoinedPrefix.lift B K fallback H _ q (certificate B K fallback H q)).trans
    (source B K fallback H q)
theorem from_entry {E : Type} (B : Carrier OWNER Data) (K : Control)
    (fallback : Data → Option PV_STX2_SliceSyntax.Program)
    (H : PV_STX2_Native.Request Data → OWNER → Reply OWNER E Data)
    (s : Store Data) (a : Nat) (parents : List Frame)
    (w : OWNER) (es : List E) (stack : List Config) :
    PV_THR2_IntrinsicState.advance B K (PV_THR2_PacketJoinedTable.table fallback) H
      (steps B K fallback H (entry s a parents w es stack)) (entry s a parents w es stack) =
      after B K fallback H (entry s a parents w es stack) := run B K fallback H _
#print axioms source
#print axioms certificate
#print axioms run
#print axioms from_entry
end PV_FN_THREAD_f361Prefix
