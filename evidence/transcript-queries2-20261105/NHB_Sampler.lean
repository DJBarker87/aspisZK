import NHB_BlockTrace
set_option autoImplicit false
noncomputable section
namespace AspisR1.NHB_Sampler
open Aeneas Aeneas.Std Result
open NGQ_SamplerDriver

def port (out : Out) : core.result.Result (Array U32 22#usize × Bytes32)
    AspisR1PublicPreparation.aspis_core.transcript.QuerySampleError :=
  match out with
  | .Ok value => .Ok value
  | .Err error => .Err (NGQ_SamplerPacket.errorPort error)

/-- Full Result association for the SAME eight blocks and eight advances.
The trace supplies local native edges, not a target sampler equality. -/
theorem decode_source (blocks advances : Blocks) (out : Out)
    (edges : NHB_BlockTrace.Trace advances
      (blocks.val.zip [0#usize,1#usize,2#usize,3#usize,4#usize,5#usize,6#usize,7#usize])
      NGQ_SamplerPacket.initial out) :
    NGQ_SamplerPacket.decode blocks advances=ok (port out) := by
  have run := NHB_BlockTrace.walk_source edges
  unfold NGQ_SamplerPacket.decode
  rw [NGQ_SamplerDriver.source,run,bind_tc_ok]
  cases out <;> rfl

/-- The installed cohort decoder is fixed; the native relation cannot install
an independently selected output or a convenient decoder boundary. -/
theorem cohort_source (blocks advances : Blocks) (out : Out)
    (edges : NHB_BlockTrace.Trace advances
      (blocks.val.zip [0#usize,1#usize,2#usize,3#usize,4#usize,5#usize,6#usize,7#usize])
      NGQ_SamplerPacket.initial out) :
    Query31ConcreteMaterializedSchedule.actualConcreteDecode
      NGQ_SamplerPacket.initial blocks advances=ok (port out) := by
  rw [← NGQ_SamplerPacket.adopted_decoder]
  exact decode_source blocks advances out edges

#print axioms decode_source
#print axioms cohort_source
end AspisR1.NHB_Sampler
end
