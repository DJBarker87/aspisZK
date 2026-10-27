import R1Z.PV_RunJoin_TrustModels
import R1Z.PV_RunJoin_DeployedFixtures
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_TrustFixtures
open PV_RunJoin_TrustBoundary PV_RunJoin_OsWorld
open PV_RunJoin_CanonicalFixtures
local instance : CharP Scalar 2147483647 :=
  charP_of_injective_algebraMap (algebraMap (ZMod AspisCircleGroupOrder.P) Scalar).injective
    AspisCircleGroupOrder.P
abbrev Coins := (Fin 128 → ProverCommitPublicNonce40.Raw) × Unit

def laws : Laws Unit Nat Unit Nat Nat where
  entropyDraw := fun _ _ _ => True
  open64 := fun _ _ _ _ _ => True
  read := fun _ _ _ _ => True
  write := fun _ _ _ _ => True
  sync := fun _ _ _ => True
  close := fun _ _ _ => True
  time := fun _ _ => True
  worker := fun _ _ => True

/-- All-error draws are compatible with the environmental signature and
its interpretation. E1 constrains successful raw bytes; it does not assert
that a successful OS return occurs. Option A is therefore an extra premise. -/
def errorWorld : World Unit Nat Unit Nat Nat where
  entropy := fun _ => (fun _ => 0,some ())
  entropyUsed := 0
  files := []
  fileUsed := 0
  time := []
  timeUsed := 0
  workers := []
  workerUsed := 0

/-- Source fixture witness is retained in the observation. This establishes
logical consistency on each mathematical fibre; it does not install native
release bytes, source selection or a trace-simulation proof. -/
def data (isWithdrawal : Bool) :=
  model (fun _ _ => ()) (Equiv.refl Coins)
    (fun _ : Coins => {
      initial := errorWorld
      calls := [(errorWorld,.entropy ⟨0,by decide⟩ (errorWorld.entropy ⟨0,by decide⟩))]
      final := {errorWorld with entropyUsed := 1}
      filesystem := ⟨[],0,[]⟩
      payload := if isWithdrawal then withdrawal else transfer })

theorem satisfies (isWithdrawal : Bool) : PV_RunJoin_TrustItems (data isWithdrawal) :=
  model_satisfies (fun _ _ => ()) (Equiv.refl Coins) _

theorem both_fibres {CommitHandle : Type} (a b : CommitHandle) :
    (∃ wt ww : (BuilderSource.prover (K := Scalar)).Instance,
      (BuilderSource.prover (K := Scalar)).public wt =
        (PV_RunJoin_DeployedFixtures.transferX a).1 ∧
      (BuilderSource.prover (K := Scalar)).public ww =
        (PV_RunJoin_DeployedFixtures.withdrawalX b).1) ∧
    PV_RunJoin_TrustItems (data false) ∧ PV_RunJoin_TrustItems (data true) :=
  ⟨PV_RunJoin_DeployedFixtures.fibres a b,satisfies false,satisfies true⟩

theorem error_is_admitted :
    nativeCall (replayNative laws) errorWorld
      (.entropy ⟨0,by decide⟩ (errorWorld.entropy ⟨0,by decide⟩)) :=
  ⟨rfl,rfl,True.intro⟩

theorem error_tag : (errorWorld.entropy ⟨0,by decide⟩).2 = some () := rfl

#print axioms satisfies
#print axioms both_fibres
#print axioms error_is_admitted
#print axioms error_tag
end R1Z.PV_RunJoin_TrustFixtures
