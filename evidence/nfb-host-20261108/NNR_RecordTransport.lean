import NNR_NoAbort
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNR_RecordTransport
open Aeneas Aeneas.Std Result VTop_Stages NJU_CommonObserved
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open NLT_NativeInvocation NNH_NativeOracleSlots
variable (H : Bytes → State) (pda : List RSL.Bytes → RSL.B32 → Option RSL.B32)
 (k : Except RSL.ProgramError UInt64) (r : NP6_StdModel.Reservation)

theorem window {X : Type} (d : aspis_core.digest.Digest32 X) (hash : X)
 (pub proof ck : Slice U8) (len : proof.val.length = 57607)
 (value : core.result.Result Unit verifier.Error) (records : List (Occurrence (part H pda k r) d hash))
 (native : Invocation (part H pda k r) d hash
  (NLT_NativeSource.skeleton (part H pda k r) d pub proof ck hash) (.ok value) records)
 (record : Occurrence (part H pda k r) d hash) (member : record ∈ records) :
 NLT_NativeWindows.window (part H pda k r) d hash record.entered record.input =
 NLT_NativeWindows.window H d hash record.entered record.input := by
 rcases record with ⟨e,input,detail⟩
 cases e with
 | resume => rfl
 | powers => rfl
 | inactive => rfl
 | geometry => rfl
 | pending => rfl
 | query => rfl
 | flush => rfl
 | finish => rfl
 | merkle pr p folded reply =>
  have domain := NNR_C04Domain.at_record (part H pda k r) d pub proof ck hash len (.ok value)
   records native ⟨.merkle pr p folded reply,input,detail⟩ member pr p folded
   (NLP_NativeMerkle.action (part H pda k r) d pr p folded 1#usize hash) rfl
  have returned := NNR_NoAbort.returned (part H pda k r) d pub proof ck hash len value
   records native ⟨.merkle pr p folded reply,input,detail⟩ member
  obtain ⟨inside,out,child⟩ := NNR_NoAbort.child (part H pda k r) pr p folded _ detail returned
  exact NNH_NativeOracleWindow.merkle H pda k r d hash pr domain.2.1
   (NLP_RootCodec.parsed pr (Port3_BatchStage.root1 p)) (NLP_RootCodec.wire _ _)
   p folded reply input domain.2.2 inside out child

def record {X : Type} {d : aspis_core.digest.Digest32 X} {hash : X}
 (o : Occurrence (part H pda k r) d hash)
 (equal : NLT_NativeWindows.window (part H pda k r) d hash o.entered o.input =
  NLT_NativeWindows.window H d hash o.entered o.input) : Occurrence H d hash :=
 ⟨o.entered,o.input,equal ▸ NNH_NativeOracleDetail.transport H pda k r o.detail⟩

theorem actual {X : Type} {d : aspis_core.digest.Digest32 X} {hash : X}
 (o : Occurrence (part H pda k r) d hash)
 (equal : NLT_NativeWindows.window (part H pda k r) d hash o.entered o.input =
  NLT_NativeWindows.window H d hash o.entered o.input) :
 NLT_NativeInvocation.actual (record H pda k r o equal) = NLT_NativeInvocation.actual o := equal.symm
#print axioms window
#print axioms record
#print axioms actual
end AspisR1.NNR_RecordTransport
end
