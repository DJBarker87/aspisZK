import PV_EVH_OperatorFrames
import PV_EVH_OpPrivateSalts
import PV_EVH_PrivateSaltsStep
import PV_EVH_OpPrivateSaltStep
import PV_EVH_PrefixLoop
set_option autoImplicit false
noncomputable section
namespace PV_EVH_OpPrivateSaltsFlow
open Aeneas Aeneas.Std ProverRwFull PV_EVH_World
open PV_EVH_Prefix (P FinishedView)
variable [ExternalTypes] [ExternalFuns]
abbrev Reserved := aspis_prover.state_only_entropy.ReservedStateOnlyAttemptSecrets
abbrev Context := aspis_core.state_only_hiding.StateOnlyHidingContext
abbrev Hash := Slice (Slice U8) → Result (Array U8 32#usize)
abbrev Salts := core.result.Result (alloc.vec.Vec (Array U8 32#usize)) verifier.Error

def stepCallees (c : PV_EVH_OpPrivateSaltStep.Callees) : PV_EVH_PrivateSaltsStep.Callees where
  derive_private_salt_step_OPEN := fun reserved context hash tag index salts =>
    PV_EVH_OpPrivateSaltStep.run reserved context hash tag index salts c

theorem stepCallees_fixed (c : PV_EVH_OpPrivateSaltStep.Callees)
    (hc : PV_EVH_OpPrivateSaltStep.Compatible c) :
    PV_EVH_PrivateSaltsStep.Compatible (stepCallees c) where
  derive_private_salt_step_fixed := fun reserved context hash tag index salts =>
    PV_EVH_OpPrivateSaltStep.run_fixed reserved context hash tag index salts c hc

def loop (fuel : Nat) (reserved : Reserved) (context : Context) (hash : Hash)
    (tag : U8) (count : Usize) (result : Salts) (index : Usize)
    (c : PV_EVH_OpPrivateSaltStep.Callees) : P Salts :=
  PV_EVH_PrefixLoop.loop
    (fun (state : Salts × Usize) =>
      PV_EVH_PrivateSaltsStep.run reserved context hash tag count state.1 state.2 (stepCallees c))
    fuel (result, index)

theorem loop_fixed (fuel : Nat) (reserved : Reserved) (context : Context) (hash : Hash)
    (tag : U8) (count : Usize) (result : Salts) (index : Usize)
    (c : PV_EVH_OpPrivateSaltStep.Callees) (hc : PV_EVH_OpPrivateSaltStep.Compatible c) :
    FinishedView (loop fuel reserved context hash tag count result index c)
      (prover.derive_private_salts_loop reserved context hash tag count result index) := by
  apply PV_EVH_PrefixLoop.fixed_recursive
    (fun (state : Salts × Usize) =>
      PV_EVH_PrivateSaltsStep.run reserved context hash tag count state.1 state.2 (stepCallees c))
    (fun (state : Salts × Usize) =>
      prover.derive_private_salts_loop.body reserved context hash tag count state.1 state.2)
    (fun (state : Salts × Usize) =>
      prover.derive_private_salts_loop reserved context hash tag count state.1 state.2)
  · rintro ⟨result, index⟩
    unfold prover.derive_private_salts_loop
    rw [Aeneas.Std.loop.eq_def]
    dsimp only
    cases h : prover.derive_private_salts_loop.body reserved context hash tag count result index with
    | ok cf => cases cf <;> rfl
    | fail e => rfl
    | div => rfl
  · rintro ⟨result, index⟩
    exact PV_EVH_PrivateSaltsStep.run_fixed reserved context hash tag count result index
      (stepCallees c) (stepCallees_fixed c hc)

structure Callees where
  FIBRE_COUNT_OPEN : P Usize
  reserve_OPEN : ∀ {T : Type} (A : Type) (v : alloc.vec.Vec T) (n : Usize),
    P ((core.result.Result Unit alloc.collections.TryReserveError) × alloc.vec.Vec T)

structure Compatible (c : Callees) : Prop where
  count_fixed : FinishedView c.FIBRE_COUNT_OPEN aspis_core.r0.FIBRE_COUNT
  reserve_fixed : ∀ {T : Type} (A : Type) (v : alloc.vec.Vec T) (n : Usize),
    FinishedView (c.reserve_OPEN A v n) (alloc.vec.Vec.try_reserve_exact A v n)

def install (fuel : Nat) (c : Callees) (step : PV_EVH_OpPrivateSaltStep.Callees) (frames : PV_EVH_OperatorFrames.Frames) :
    PV_EVH_OpPrivateSalts.Callees where
  op11_OPEN := PV_EVH_OperatorFrames.map frames
  op12_OPEN := PV_EVH_OperatorFrames.mapErr frames
  FIBRE_COUNT_OPEN := c.FIBRE_COUNT_OPEN
  op32_OPEN := c.reserve_OPEN
  derive_private_salts_loop_OPEN := fun reserved context hash tag count result index =>
    loop fuel reserved context hash tag count result index step

theorem install_fixed (fuel : Nat) (c : Callees) (step : PV_EVH_OpPrivateSaltStep.Callees)
    (hc : Compatible c) (hs : PV_EVH_OpPrivateSaltStep.Compatible step)
    (frames : PV_EVH_OperatorFrames.Frames) (hf : PV_EVH_OperatorFrames.Compatible frames)
    (selected : PV_EVH_OperatorFrames.Selection (inferInstance : ExternalFuns)) :
    PV_EVH_OpPrivateSalts.Compatible (install fuel c step frames) where
  op11_fixed := fun inst r closure => PV_EVH_OperatorFrames.map_fixed _ selected frames hf inst r closure
  op12_fixed := fun inst r closure => PV_EVH_OperatorFrames.mapErr_fixed _ selected frames hf inst r closure
  FIBRE_COUNT_fixed := hc.count_fixed
  op32_fixed := hc.reserve_fixed
  derive_private_salts_loop_fixed := fun reserved context hash tag count result index =>
    loop_fixed fuel reserved context hash tag count result index step hs
#print axioms stepCallees_fixed
#print axioms loop_fixed
#print axioms install_fixed
end PV_EVH_OpPrivateSaltsFlow
