import R1Z.PV_RunJoin_ParentNoopRounds
import R0Z.PoseidonInternal
import R1Z.PV_RunJoin_FixtureRecords

/-! Symbolic lifting of finite copy-round folds. Every round uses the proved
single-round theorem; no concrete recurrence or field table is normalized. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_ParentRoundLift
open Aeneas Aeneas.Std Result R0Z.WriterRefine R0Z.PoseidonRefine
open PV_Src_PortSboxStep PV_RunJoin_ParentNoopRounds
abbrev M := PV_RunJoin_FixtureRecords.M

def fullModel (xs : List (Usize × State)) (s : Fin 16 → M) : Fin 16 → M :=
  match xs with
  | [] => s
  | (_,c)::tail => fullModel tail (R0P.poseidonFullRound s (liftA c))

def internalModel (xs : List (Usize × U32)) (s : Fin 16 → M) : Fin 16 → M :=
  match xs with
  | [] => s
  | (_,c)::tail => internalModel tail (R0P.poseidonInternalRound s (liftU c))

theorem full_lift (xs : List (Usize × State)) (s : State) (hs : Canonical s) :
    ∃ out, full xs s = ok out ∧ Canonical out ∧
      liftA (K := M) out = fullModel xs (liftA s) := by
  induction xs generalizing s with
  | nil => exact ⟨s,rfl,hs,rfl⟩
  | cons head tail ih =>
    rcases head with ⟨index,c⟩
    obtain ⟨out,ho,hcan⟩ := PV_RunJoin_SourceRoundFold.full_total s c
    obtain ⟨other,hh,hfield⟩ := full_round_lift (K := M) s c
    have he : other=out := Result.ok.inj (hh.symm.trans ho)
    subst other
    have hf : liftA (K := M) out = R0P.poseidonFullRound (liftA s) (liftA c) :=
      funext hfield
    obtain ⟨last,hl,hcl,hfl⟩ := ih out hcan
    refine ⟨last,?_,hcl,?_⟩
    · simp only [full,ho,bind_tc_ok,hl]
    · simpa only [fullModel,hf] using hfl

theorem internal_lift (xs : List (Usize × U32)) (s : State) (hs : Canonical s) :
    ∃ out, internal xs s = ok out ∧ Canonical out ∧
      liftA (K := M) out = internalModel xs (liftA s) := by
  induction xs generalizing s with
  | nil => exact ⟨s,rfl,hs,rfl⟩
  | cons head tail ih =>
    rcases head with ⟨index,c⟩
    obtain ⟨out,ho,hcan⟩ := PV_RunJoin_SourceInternalRounds.total s c
    obtain ⟨other,hh,hfield⟩ := internal_round_lift (K := M) s c R0PoseidonCopy.INTERNAL_SHIFTS
      PV_Src_PortInternalCopy.shifts_bound PV_Src_PortInternalCopy.shifts_model
    have he : other=out := Result.ok.inj (hh.symm.trans ho)
    subst other
    have hf : liftA (K := M) out = R0P.poseidonInternalRound (liftA s) (liftU c) :=
      funext hfield
    obtain ⟨last,hl,hcl,hfl⟩ := ih out hcan
    refine ⟨last,?_,hcl,?_⟩
    · simp only [internal,ho,bind_tc_ok,hl]
    · simpa only [internalModel,hf] using hfl

#print axioms full_lift
#print axioms internal_lift
end R1Z.PV_RunJoin_ParentRoundLift
