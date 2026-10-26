import F3X_FixtureRuntime
set_option autoImplicit false
noncomputable section
namespace AspisR1.RPx_RuntimePrefix
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open F3T_Runtime F3T_ByteCarrier

def prepend (prelude : Program Bytes State Unit) (runtime : Runtime) : Runtime :=
  bind prelude fun _=>runtime

theorem evaluation (prelude : Program Bytes State Unit) (runtime : Runtime) (H : Bytes → State) :
    eval H (prepend prelude runtime) =
      ((eval H prelude).1 ++ (eval H runtime).1,(eval H runtime).2) := by
  rw [prepend,eval_bind]

/-- Accepted-run binding says nothing about the runtime's outer query log.
Any prelude can be prepended without violating the exact current interface. -/
theorem binding {F C : Type} (c : DrvC_Installation.Configuration F C)
    (D : LiteralByteProtocol.Decoder) (rust : F3T_TwoPass.Verifier)
    (P : ByteProver) (runtime : Runtime) (law : StoredCarrierBinding c D rust P runtime)
    (prelude : Program Bytes State Unit) :
    StoredCarrierBinding c D rust P (prepend prelude runtime) := by
  intro H run observed accepted
  rw [evaluation] at observed
  exact law H run observed accepted

/-- The issue persists for a genuinely accepting runtime: an existing
accepted observation is preserved by arbitrary query prefixes. -/
theorem acceptance (prelude : Program Bytes State Unit) (runtime : Runtime)
    (H : Bytes → State) (run : F3T_Experiment.RunView)
    (observed : (eval H runtime).2=some run) (accepted : run.2.2=true) :
    (eval H (prepend prelude runtime)).2=some run ∧ run.2.2=true := by
  rw [evaluation]
  exact ⟨observed,accepted⟩

#print axioms evaluation
#print axioms binding
#print axioms acceptance
end AspisR1.RPx_RuntimePrefix
end
