import RPz7_F3T_Runtime
set_option autoImplicit false
noncomputable section
namespace AspisR1.SCC_Physical
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open F3T_Experiment F3T_TwoPass

/-- Corrected first-pass obligation, exposed for diagnosis only. This is NOT
an adopted runtime trust item or a proved deployed instance. -/
def FirstPassBinding (rust : Verifier) (P : Prover) (runtime : F3T_Runtime.Runtime) : Prop :=
  ∀ H run, (eval H runtime).2 = some run → run.2.2 = true →
    run = eval H (originalWith rust P)

/-- A strictly smaller necessary observation: the runtime's stored input is
that of the headline prover in the SAME oracle world. Not sufficient for the
full first-pass obligation, and not adopted as trust. -/
def StoredInputLaw (P : Prover) (runtime : F3T_Runtime.Runtime) : Prop :=
  ∀ H run, (eval H runtime).2 = some run → run.2.2 = true →
    run.2.1.stored = (eval H P).2.stored

theorem stored_of_first (rust : Verifier) (P : Prover) (runtime : F3T_Runtime.Runtime)
    (binding : FirstPassBinding rust P runtime) : StoredInputLaw P runtime := by
  intro H run observed accepted
  have same := congrArg (fun v : RunView => v.2.1.stored)
    (binding H run observed accepted)
  rw [F3T_TwoPass.original_eval] at same
  exact same

/-- Pure diagnostic returned view. It makes NO assertion that a real verifier
accepted this input; that missing association is exactly what is tested. -/
def changedInput (i : F3_Model.Input) : F3_Model.Input :=
  {i with stored := 0 :: i.stored}

def acceptedView (i : F3_Model.Input) : RunView := ([],(changedInput i,true))

def constantRuntime (i : F3_Model.Input) : F3T_Runtime.Runtime :=
  .done (some (acceptedView i))

theorem changed_stored (i : F3_Model.Input) : (changedInput i).stored ≠ i.stored := by
  intro same
  have lengths := congrArg List.length same
  change i.stored.length + 1 = i.stored.length at lengths
  omega

/-- For every fixed prover and world, an unrestricted runtime binder can
return an accepted view with different stored bytes. This works for ANY rust,
including the exact installed source, without supposing it accepts a fixture.
The witness is a constant program: no additional oracle access is fabricated. -/
theorem accepted_unassociated (P : Prover) (H : Bytes → State) :
    ∃ (runtime : F3T_Runtime.Runtime) (run : RunView),
      eval H runtime = ([],some run) ∧ run.2.2 = true ∧
      run.2.1.stored ≠ (eval H P).2.stored ∧
      ¬ StoredInputLaw P runtime ∧
      (∀ rust : Verifier, ¬ FirstPassBinding rust P runtime) := by
  refine ⟨constantRuntime (eval H P).2,acceptedView (eval H P).2,rfl,rfl,
    changed_stored _,?_,?_⟩
  · intro law
    exact changed_stored _ (law H _ rfl rfl)
  · intro rust binding
    exact changed_stored _ (stored_of_first rust P _ binding H _ rfl rfl)

/-- Retain any already satisfied runtime-independent conditions. This does
not claim joint satisfiability of every Rc5 cryptographic/extraction premise. -/
theorem preserve_conditions (conditions : Prop) (satisfied : conditions)
    (P : Prover) (H : Bytes → State) :
    conditions ∧ ∃ (runtime : F3T_Runtime.Runtime) (run : RunView),
      eval H runtime = ([],some run) ∧ run.2.2 = true ∧
      run.2.1.stored ≠ (eval H P).2.stored ∧
      ¬ StoredInputLaw P runtime ∧
      (∀ rust : Verifier, ¬ FirstPassBinding rust P runtime) :=
  ⟨satisfied,accepted_unassociated P H⟩

#print axioms stored_of_first
#print axioms changed_stored
#print axioms accepted_unassociated
#print axioms preserve_conditions
end AspisR1.SCC_Physical
end
