import R1Z.ProverCommitControl28
/-! An ordered observer accompanies the state transformer, independently of
CoinOracle's deduplicated recording map. It retains repeated calls in order. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverCommitLogged28
open Aeneas Aeneas.Std Result ProverCommitStateLift28 ProverCommitCoinCall27
abbrev Bytes32 := ProverCommitCoinCall27.Bytes32
abbrev History := List (Parts × Bytes32)
abbrev LoggedMachine := Machine × History

def logged {S : Type} (effect : Effect S) : Effect (S × History) := fun state parts => do
  let (answer,next) ← effect state.1 parts
  ok (answer,(next,state.2 ++ [(parts,answer)]))

theorem logged_exact {S : Type} (actual reference : Effect S)
    (calls : ∀ s p, actual s p = reference s p) :
    ∀ s p, logged actual s p = logged reference s p := by
  intro s p
  unfold logged
  rw [calls]

def dictionary (effect : Effect Machine) : Unit → Parts → Port LoggedMachine Bytes32 :=
  fun _ parts => read (logged effect) parts

def queries (s : ProverCommitControl28.State) (row : U8) (payload : Slice U8) :=
  ProverCommitControlProgram28.queries (dictionary ProverCommitControl28.extracted)
    ProverCommitQuery26.policy s row payload

def tail (state : Bytes32) (sem : ProverCommitControl28.Values)
    (z : ProverCommitControl28.Points) (records : AspisR1SimControl21.sim.Records)
    (variant : AspisR1SimControl21.transport.Variant) :=
  ProverCommitControlProgram28.tail (dictionary ProverCommitControl28.extracted)
    ProverCommitQuery26.policy () state sem z records variant

theorem query_history (s : ProverCommitControl28.State) (row : U8) (payload : Slice U8)
    (machine : LoggedMachine) : queries s row payload machine =
    ProverCommitControlProgram28.queries (dictionary ProverCommitControl28.reference)
      ProverCommitQuery26.policy s row payload machine := by
  exact install _ _ (logged_exact _ _ call_exact)
    (fun e => ProverCommitControlProgram28.queries (fun (_ : Unit) p => read e p)
      ProverCommitQuery26.policy s row payload) machine

theorem tail_history (state : Bytes32) (sem : ProverCommitControl28.Values)
    (z : ProverCommitControl28.Points) (records : AspisR1SimControl21.sim.Records)
    (variant : AspisR1SimControl21.transport.Variant) (machine : LoggedMachine) :
    tail state sem z records variant machine =
    ProverCommitControlProgram28.tail (dictionary ProverCommitControl28.reference)
      ProverCommitQuery26.policy () state sem z records variant machine := by
  exact install _ _ (logged_exact _ _ call_exact)
    (fun e => ProverCommitControlProgram28.tail (fun (_ : Unit) p => read e p)
      ProverCommitQuery26.policy () state sem z records variant) machine

/-- Literal replay reset: same finite tape, reset cursor, fresh recording map,
clear collision; the observer retains the prefix from before replay. -/
def replayReset (state : LoggedMachine) : LoggedMachine :=
  (⟨state.1.coins,0#usize,some (fun _ => none),false⟩,state.2)

theorem reset_tape (state : LoggedMachine) : (replayReset state).1.coins = state.1.coins := rfl
theorem reset_history (state : LoggedMachine) : (replayReset state).2 = state.2 := rfl

theorem reset_then {A : Type} (continuation : Port LoggedMachine A) (state : LoggedMachine) :
    ((modify replayReset : Port LoggedMachine Unit) >>= fun _ => continuation) state =
    continuation (replayReset state) := by rfl

#print axioms logged_exact
#print axioms query_history
#print axioms tail_history
#print axioms reset_tape
#print axioms reset_history
#print axioms reset_then
end R1Z.ProverCommitLogged28
