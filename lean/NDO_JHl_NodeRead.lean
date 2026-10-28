import NDO_JHl_WeightFormula
import NDO_JHk_LineRead
set_option autoImplicit false
noncomputable section
namespace AspisR1.JHl_NodeRead
open Aeneas Aeneas.Std Result AspisR1Stage2

theorem source (i : Fin 10) (p : verifier.Prepared) (a out : verifier.Accumulator)
    (b after : verifier.BatchedWeights)
    (next : a.next=JGw_GeometryReads.cursor i)
    (o : Port4C_QueryValues.Observation JHa_AllQueries.ops JFx_NativeBytes.proof p a out
      JFr_TX2_Powers.value none (JGp_Geometry.value () JGp_Seeds.geometry) b after) :
    o.node=JHl_WeightFormula.node i := by
  have hz := o.z_read
  rw [next] at hz
  have z : o.z=(JGp_Rows.value i).lineZ := Result.ok.inj
    (hz.symm.trans (Classical.choose_spec (JGw_GeometryReads.source () JGp_Seeds.geometry i)).2.1)
  have hs : AspisR1Qm31ArithmeticProbe.field.M31.mul o.z o.z=ok o.square := o.square_call
  have hd : AspisR1Qm31ArithmeticProbe.field.M31.double o.square=ok o.doubled := o.double_call
  have one : o.one=1#u32 := Result.ok.inj o.one_call.symm
  have hn : AspisR1Qm31ArithmeticProbe.field.M31.sub o.doubled 1#u32=ok o.node := by
    rw [←one]
    exact o.node_call
  have call : JFv_TX2_NodeCall.sourceCall o.z=ok o.node := by
    simp only [JFv_TX2_NodeCall.sourceCall,hs,hd,hn,bind_tc_ok]
  rw [z] at call
  exact Result.ok.inj (call.symm.trans (JHl_WeightFormula.node_call i))
#print axioms source
end AspisR1.JHl_NodeRead
end
