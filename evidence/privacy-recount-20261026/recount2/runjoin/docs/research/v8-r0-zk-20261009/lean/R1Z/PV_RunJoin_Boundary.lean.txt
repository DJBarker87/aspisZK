import R1Z.PV_RunJoin_Deployed
import R1Z.PV_RunJoin_E1Joint
import R1Z.ProverCommitPublicNonce40
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_Boundary
open Aeneas Aeneas.Std Result ProverRwRngCaller
open R0Z R0Z.FsStatement R0Z.JointView R1Z.GamesR1
local instance : NativeTypes := PV_RunJoin_CallerWorld.nativeTypes
local instance : ErasureFns := ⟨fun _ value => .ok value,fun _ value => .ok value⟩
local notation "K" => PrivacyR1AcctBasis.K
variable [ProverRwFull.ExternalTypes]

/-- Boundary DATA, not certificates. Each corresponding source/effect law is
exposed as a separate named row field at the endpoint. In particular `draw`
is a world-threaded Draw64, never a pure getrandom ExternalFuns entry. -/
structure Data {CommitHandle Aux Coins N L C : Type}
    (runtime : PV_RunJoin_Deployed.Runtime CommitHandle Aux Coins N L C)
    (Context Rest : Type) where
  sourceBody : (h : HonestProver K) → (x : Statement K CommitHandle) → h.Instance →
    PV_RunJoin_UnifiedRetry.SourceBody (PV_RunJoin_Deployed.State N L C)
  draw : Draw64 Tape
  law : Context → ProverCommitPublicNonce40.Raw → ℚ
  frame : Fin 128 → (Fin 128 → ProverCommitPublicNonce40.Raw) × Rest → Context
  coordinates : Coins ≃ (Fin 128 → ProverCommitPublicNonce40.Raw) × Rest
  nativeWeight : Coins → ℚ
  ledger : PV_RunJoin_Deployed.State N L C → ProverCommitLedger36.State
  reservation : ProverRwRetryModel.Secret → PV_RunJoin_Deployed.State N L C → Option ProverCommitLedger36.Path
  schedule : ProverCommitLedger36.Schedule
  unix : Bool
  fault : ProverRwRetryModel.Secret → PV_RunJoin_Deployed.State N L C →
    ProverCommitEnvironment35.Kind → ProverCommitLedger36.Action

/-- Equality of native completion density to the E1-derived uniform graph
law. The pointwise native factorization remains V339; E1 is exactly V329.
No uniform law for OS error tags or for arbitrary initial ledgers is inferred. -/
theorem density_uniform {CommitHandle Aux Coins N L C Context Rest : Type}
    [Fintype Coins] [Fintype Rest]
    (runtime : PV_RunJoin_Deployed.Runtime CommitHandle Aux Coins N L C)
    (d : Data runtime Context Rest)
    (e1 : ProverCommitPublicNonce40.E1 d.law)
    (factorization : ∀ c, d.nativeWeight c =
      PV_RunJoin_E1Joint.weight 128 d.law d.frame d.coordinates c) (c : Coins) :
    d.nativeWeight c = 1 / (Fintype.card Coins : ℚ) :=
  PV_RunJoin_E1Joint.native_density_uniform 128 d.law e1 d.frame d.coordinates d.nativeWeight factorization c

/-- V036's boundary calculation for the SAME explicit world carrier used by
cp. This weighted law is meaningful for native execution only after its
factorization and primitive/world associations have been proved. -/
theorem native_world_mean {CommitHandle Aux Coins N L C Context Rest : Type}
    [Fintype Coins] [Fintype Rest]
    (runtime : PV_RunJoin_Deployed.Runtime CommitHandle Aux Coins N L C)
    (d : Data runtime Context Rest)
    (e1 : ProverCommitPublicNonce40.E1 d.law)
    (factorization : ∀ c, d.nativeWeight c =
      PV_RunJoin_E1Joint.weight 128 d.law d.frame d.coordinates c)
    (f : PV_RunJoin_Deployed.World runtime → ℚ) :
    (∑ s, d.nativeWeight s.coins * f s) = mean f := by
  simp_rw [density_uniform runtime d e1 factorization]
  unfold mean
  rw [Fintype.card_congr (PV_RunJoin_Deployed.coordinates runtime)]
  simp only [one_div_mul_eq_div,Finset.sum_div]

#print axioms density_uniform
#print axioms native_world_mean
end R1Z.PV_RunJoin_Boundary
