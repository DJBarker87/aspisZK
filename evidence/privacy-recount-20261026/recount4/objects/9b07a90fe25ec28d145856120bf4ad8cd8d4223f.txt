import R1Z.ProverCommitControlSource28
import R1Z.ProverCommitQuery26
/-! Concrete effect installation in the complete reconstructed suffix.
The token is Unit; all mutable oracle state is in the returned Machine. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverCommitControl28
open Aeneas Aeneas.Std Result AspisR1SimControl21
open ProverCommitStateLift28 ProverCommitCoinCall27
abbrev Bytes32 := ProverCommitCoinCall27.Bytes32
abbrev State := transcript.control21.Transcript Unit Unit
abbrev Values := Array aspis_core.field.QM31 25#usize
abbrev Points := Array (Array aspis_core.field.QM31 2#usize) 2#usize

def extracted : Effect Machine :=
  AspisR1CoinEffect27.CoinOracle.Insts.Effect27EffectDigest32CoinState.digest mapRecording

def reference : Effect Machine := fun s p => ok (expected s p)

def dictionary (effect : Effect Machine) : Unit → Parts → Port Machine Bytes32 :=
  fun _ parts => read effect parts

def queries (s : State) (row : U8) (payload : Slice U8) :=
  ProverCommitControlProgram28.queries (dictionary extracted) ProverCommitQuery26.policy s row payload

def tail (state : Bytes32) (sem : Values) (z : Points) (records : sim.Records)
    (variant : transport.Variant) :=
  ProverCommitControlProgram28.tail (dictionary extracted) ProverCommitQuery26.policy
    () state sem z records variant

/-- The actual state-passing machine is installed through query selection,
all native-trace writes, and both rejection and successful returned states. -/
theorem query_effects (s : State) (row : U8) (payload : Slice U8) (machine : Machine) :
    queries s row payload machine =
    ProverCommitControlProgram28.queries (dictionary reference) ProverCommitQuery26.policy
      s row payload machine := by
  exact install extracted reference call_exact
    (fun e => ProverCommitControlProgram28.queries (dictionary e)
      ProverCommitQuery26.policy s row payload) machine

/-- The same installation includes initialization, gamma/ordinary/rho policies,
query errors and the complete source trace, without a supplied call equality. -/
theorem tail_effects (state : Bytes32) (sem : Values) (z : Points)
    (records : sim.Records) (variant : transport.Variant) (machine : Machine) :
    tail state sem z records variant machine =
    ProverCommitControlProgram28.tail (dictionary reference) ProverCommitQuery26.policy
      () state sem z records variant machine := by
  exact install extracted reference call_exact
    (fun e => ProverCommitControlProgram28.tail (dictionary e) ProverCommitQuery26.policy
      () state sem z records variant) machine

#print axioms query_effects
#print axioms tail_effects
end R1Z.ProverCommitControl28
