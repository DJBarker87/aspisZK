import LIBB_Tx2TraceModel
set_option autoImplicit false
noncomputable section
namespace LIBB_Tx2ResolvedValues
/-- Functional resolved graph support. It is deliberately separate from
independent native stop-prefix transport, which is not yet installed. -/
def graph (pub proof ck : Aeneas.Std.Slice Aeneas.Std.U8) : RSL.Spec (Except LIBB_V2Carriers.VErr Unit) :=
 fun env o => o = LIBB_Tx2TraceModel.observation env pub proof ck

def evaluator (env : RSL.Env) (pub proof ck : Aeneas.Std.Slice Aeneas.Std.U8) : Except LIBB_V2Carriers.VErr Unit :=
 match (LIBB_Tx2TraceModel.observation env pub proof ck).exit with
 | .ret r => r
 | _ => .error .Checkpoint

theorem functional (pub proof ck : Aeneas.Std.Slice Aeneas.Std.U8) :
 RSL.Spec.Functional (graph pub proof ck) := by
 intro env
 exact ⟨LIBB_Tx2TraceModel.observation env pub proof ck,fun _ => Iff.rfl⟩

theorem returns (pub proof ck : Aeneas.Std.Slice Aeneas.Std.U8) (env : RSL.Env) :
 NND_Returned.Returns (graph pub proof ck) env (evaluator env pub proof ck) := by
 intro o r h hr
 subst o
 unfold evaluator
 rw [hr]
#print axioms functional
#print axioms returns
end LIBB_Tx2ResolvedValues
end
