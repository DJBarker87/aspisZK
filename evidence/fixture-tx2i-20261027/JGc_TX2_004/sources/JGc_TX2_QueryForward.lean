import JGc_TX2_QueryDictionary
import Port4C_QueryValues
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGc_TX2_QueryForward
open Aeneas Aeneas.Std Result AspisR1Stage2 Port3_NativeQueryBody

theorem source (seed : Ops) (proof : Slice U8) (p : verifier.Prepared)
    (a out : verifier.Accumulator) (g : Array SAQ_WideABI.E 29#usize)
    (geometry : verifier.QueryGeometry) (b bout : verifier.BatchedWeights)
    (calls : Port4C_QueryValues.Observation (JGc_TX2_QueryDictionary.ops seed)
      proof p a out g none geometry b bout) :
    verifier.candidate.query_values (JGc_TX2_QueryDictionary.ops seed)
      proof p a g none geometry b=ok (.Ok (out,bout)) := by
  obtain ⟨d0,hd0,_⟩ := WP.spec_imp_exists
    (Array.index_usize_spec calls.dots 0#usize (by decide))
  obtain ⟨d1,hd1,_⟩ := WP.spec_imp_exists
    (Array.index_usize_spec calls.dots 1#usize (by decide))
  obtain ⟨d2,hd2,_⟩ := WP.spec_imp_exists
    (Array.index_usize_spec calls.dots 2#usize (by decide))
  obtain ⟨d3,hd3,_⟩ := WP.spec_imp_exists
    (Array.index_usize_spec calls.dots 3#usize (by decide))
  obtain ⟨rem,hrem,hselected⟩ := calls.selected_read
  have trace : ∀ tag pos value, (JGc_TX2_QueryDictionary.ops seed).op15 tag pos value=ok () := by
    intro tag pos value
    rw [(JGc_TX2_QueryDictionary.fields seed).2.2.2.2.2.2.1]
  simp only [verifier.candidate.query_values,calls.query_read,calls.cast,
    calls.opening_read,calls.dots_read,bind_tc_ok,lift,hd0,hd1,hd2,hd3,trace,
    calls.inverse_read,calls.alpha0_read,calls.circle,calls.values_read,hrem,
    hselected,calls.comparison,Bool.false_eq_true,ite_false,calls.alpha1_read,
    calls.line,calls.z_read,calls.square_call,calls.double_call,calls.one_call,
    calls.node_call,calls.accumulate,calls.marked]
#print axioms source
end AspisR1.JGc_TX2_QueryForward
end
