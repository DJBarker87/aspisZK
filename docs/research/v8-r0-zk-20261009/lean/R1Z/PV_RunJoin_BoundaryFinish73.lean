import R1Z.PV_RunJoin_BoundarySource73
import R1Z.PV_RunJoin_BoundaryReduceValue73
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_BoundaryFinish73
open Aeneas Aeneas.Std Result ProverRwFull

theorem complete (s : ProverRwP6BoundaryStep.Acc) :
    ∃ q,PV_RunJoin_BoundarySource73.finish s=ok q ∧ PV_RunJoin_FieldData34.canonical q ∧
      q.c0.a.val=s.a.val%AspisCircleGroupOrder.P ∧ q.c0.b.val=s.b.val%AspisCircleGroupOrder.P ∧
      q.c1.a.val=s.c.val%AspisCircleGroupOrder.P ∧ q.c1.b.val=s.d.val%AspisCircleGroupOrder.P := by
  obtain ⟨a,ha,va,ca⟩ := PV_RunJoin_BoundaryReduceValue73.complete s.a
  obtain ⟨b,hb,vb,cb⟩ := PV_RunJoin_BoundaryReduceValue73.complete s.b
  obtain ⟨c,hc,vc,cc⟩ := PV_RunJoin_BoundaryReduceValue73.complete s.c
  obtain ⟨d,hd,vd,cd⟩ := PV_RunJoin_BoundaryReduceValue73.complete s.d
  refine ⟨⟨⟨a,b⟩,⟨c,d⟩⟩,?_,⟨⟨ca,cb⟩,⟨cc,cd⟩⟩,va,vb,vc,vd⟩
  simp only [PV_RunJoin_BoundarySource73.finish,ha,hb,hc,hd,bind_tc_ok,
    ProverRwP6BoundarySource.aspis_core.field.CM31.new,ProverRwDictionaryBytes.Src.complex,
    ProverRwDictionaryBytesSource.aspis_core.field.CM31.new]

#print axioms complete
end R1Z.PV_RunJoin_BoundaryFinish73
