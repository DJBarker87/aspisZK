import F3X_FixtureRuntime
set_option autoImplicit false
noncomputable section
namespace AspisR1.RPx_RuntimePrefix
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open F3T_Runtime F3T_ByteCarrier

def prepend (prefix : Program Bytes State Unit) (runtime : Runtime) : Runtime :=
  bind prefix fun _=>runtime

theorem evaluation (prefix : Program Bytes State Unit) (runtime : Runtime) (H : Bytes → State) :
    eval H (prepend prefix runtime) =
      ((eval H prefix).1 ++ (eval H runtime).1,(eval H runtime).2) := by
  rw [prepend,eval_bind]

/-- Accepted-run binding says nothing about the runtime's outer query log.
Any prefix can be prepended without violating the exact current interface. -/
theorem binding {F C : Type} (c : DrvC_Installation.Configuration F C)
    (D : LiteralByteProtocol.Decoder) (rust : F3T_TwoPass.Verifier)
    (P : ByteProver) (runtime : Runtime) (law : StoredCarrierBinding c D rust P runtime)
    (prefix : Program Bytes State Unit) :
    StoredCarrierBinding c D rust P (prepend prefix runtime) := by
  intro H run observed accepted
  rw [evaluation] at observed
  exact law H run observed accepted

/-- The issue persists for a genuinely accepting runtime: an existing
accepted observation is preserved by arbitrary query prefixes. -/
theorem acceptance (prefix : Program Bytes State Unit) (runtime : Runtime)
    (H : Bytes → State) (run : F3T_Experiment.RunView)
    (observed : (eval H runtime).2=some run) (accepted : run.2.2=true) :
    (eval H (prepend prefix runtime)).2=some run ∧ run.2.2=true := by
  rw [evaluation]
  exact ⟨observed,accepted⟩

#print axioms evaluation
#print axioms binding
#print axioms acceptance
end AspisR1.RPx_RuntimePrefix
end
