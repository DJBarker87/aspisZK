import RPz7_GExp_BatchBudget
import RPz7_GExp_SecondSource
set_option autoImplicit false
noncomputable section
namespace AspisR1.GExp_CheckpointBudget
open Aeneas Aeneas.Std Result CheckpointBytes5Effect GExp_QueryBudget

theorem raw_reader (ops : AspisR1Stage2.ResumeOps) (ck proof pub : Slice U8)
    (v : AspisR1Stage2.transport.Variant) : bounded 3 (Port8EFF_NativeReader.program ops ck proof pub v) := by
  unfold Port8EFF_NativeReader.program
  repeat' first
    | (solve | apply pure_bound)
    | (solve | apply lift_bound)
    | (apply lift_bind;intro x)
    | (query_budget_then 1
       <;> first | omega | (solve | apply read_bound) | intro x)
    | split

theorem reader (reserved : Bool) (ck proof pub : Slice U8)
    (v : VTop_Stages.transport.Variant) : bounded 3 (GExp_RetainedReader.code reserved ck proof pub v) := by
  unfold GExp_RetainedReader.code
  query_budget_then_for 3 Port8EFF_NativeReader.program
  · decide
  · exact raw_reader _ _ _ _ _
  · intro out
    exact pure_bound _ _

theorem raw_writer (p : CheckpointBytes5Writer.Prepared) (a : CheckpointBytes5Writer.Accumulator)
    (proof pub : Slice U8) : bounded 3 (CheckpointBytes5Writer.writer p a proof pub) := by
  unfold CheckpointBytes5Writer.writer
  repeat' first
    | (solve | apply pure_bound)
    | (query_budget_then 1
       <;> first | omega | (solve | apply read_bound) | intro x)

theorem writer (p : AspisR1CurrentCaller.verifier.Prepared) (a : AspisR1CurrentCaller.verifier.Accumulator)
    (proof pub : Slice U8) : bounded 3 (GExp_FirstCode.writerCode p a proof pub) := by
  unfold GExp_FirstCode.writerCode
  query_budget_then_for 3 CheckpointBytes5Writer.writer
  · decide
  · exact raw_writer _ _ _ _
  · intro out
    exact pure_bound _ _

#print axioms raw_reader
#print axioms reader
#print axioms raw_writer
#print axioms writer
end AspisR1.GExp_CheckpointBudget
end
