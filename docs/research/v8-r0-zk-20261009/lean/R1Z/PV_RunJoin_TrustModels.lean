import R1Z.PV_RunJoin_TrustOutcomes
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_TrustBoundary
open PV_RunJoin_OsWorld PV_RunJoin_NativeEffectInterface
variable {E File Reply Time Worker Context Coins Rest Observation : Type}
variable [DecidableEq File] [Fintype Rest]

/-- A mathematical realization; not evidence about Linux or release bytes. -/
def replayNative (laws : Laws E File Reply Time Worker) : Native E File Reply Time Worker where
  entropyDraw := EntropyAllowed laws
  open64 := laws.open64
  read := laws.read
  write := laws.write
  sync := laws.sync
  close := laws.close
  time := laws.time
  worker := laws.worker

theorem replayIdentity (laws : Laws E File Reply Time Worker) :
    Identity (replayNative laws) laws where
  entropy := fun _ _ _ => Iff.rfl
  open64 := fun _ _ _ _ _ _ _ => Iff.rfl
  read := fun _ _ _ _ _ _ => Iff.rfl
  write := fun _ _ _ _ _ _ => Iff.rfl
  sync := fun _ _ _ _ _ => Iff.rfl
  close := fun _ _ _ _ _ => Iff.rfl
  time := fun _ _ _ _ => Iff.rfl
  worker := fun _ _ _ _ => Iff.rfl

def model
    (frame : Fin 128 → (Fin 128 → ProverCommitPublicNonce40.Raw) × Rest → Context)
    (coordinates : Coins ≃ (Fin 128 → ProverCommitPublicNonce40.Raw) × Rest)
    (observation : Coins → PV_RunJoin_TrustBoundary.Observation E File Reply Time Worker Observation) :
    Data E File Reply Time Worker Context Coins Rest Observation where
  law := fun _ _ => 1 / (Fintype.card ProverCommitPublicNonce40.Raw : ℚ)
  frame := frame
  coordinates := coordinates
  nativeWeight := PV_RunJoin_E1Joint.weight 128
    (fun (_ : Context) (_ : ProverCommitPublicNonce40.Raw) =>
      1 / (Fintype.card ProverCommitPublicNonce40.Raw : ℚ)) frame coordinates
  nativeObservation := observation
  extractedObservation := observation

theorem model_satisfies
    (frame : Fin 128 → (Fin 128 → ProverCommitPublicNonce40.Raw) × Rest → Context)
    (coordinates : Coins ≃ (Fin 128 → ProverCommitPublicNonce40.Raw) × Rest)
    (observation : Coins → PV_RunJoin_TrustBoundary.Observation E File Reply Time Worker Observation) :
    PV_RunJoin_TrustItems (model frame coordinates observation) where
  entropy_law := fun _ _ => rfl
  entropy_kernel := fun _ => rfl
  observation := fun _ => rfl

/-- Complete native/extracted observation equality entails every projection,
including the filesystem/E2 decoder and BOTH V038 view projections. Keeping
separate trust fields for these same projections would duplicate this fact. -/
theorem observation_projection
    (d : Data E File Reply Time Worker Context Coins Rest Observation)
    (T : PV_RunJoin_TrustItems d) {A : Type} (project : PV_RunJoin_TrustBoundary.Observation E File Reply Time Worker Observation → A) (c : Coins) :
    project (d.nativeObservation c) = project (d.extractedObservation c) :=
  congrArg project (T.observation c)

#print axioms replayIdentity
#print axioms model_satisfies
#print axioms observation_projection
end R1Z.PV_RunJoin_TrustBoundary
