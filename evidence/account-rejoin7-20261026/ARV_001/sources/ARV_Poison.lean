import ARU_CoverageQuantifiers
set_option autoImplicit false
noncomputable section
namespace AspisR1.ARV_Poison
open Aeneas Aeneas.Std Result S2Trust S2W_D189Entry S2W_D189Wrappers
/-- Change only the lamports-cell identity, invisible to owned snapshots. -/
def entry (e : Entry) : Entry :=
  {e with handles := fun a => ((e.handles a).1,(e.handles a).1)}

theorem snapshot (e : Entry) (a n m : Nat) :
    (entry e).snapshot a n m = e.snapshot a n m := rfl

theorem sizes (e : Entry) (n : Nat) (s : Nat → Nat × Nat) :
    admittedSizes (entry e) n s = admittedSizes e n s := rfl

theorem owned (e : Entry) : (entry e).second secondSizes = e.second secondSizes := rfl

theorem invalid (e : Entry) : ¬ Valid (entry e).heap := by
  intro valid
  have separate := valid.2.2.2 0 rfl
  exact separate.1 rfl

theorem no_admission {W : Type} (L : Library W (Nat → Record)) (e : Entry) (w : W) (n : Nat) :
    ¬ S2W_D189Consolidation.RuntimeEntrypointAdmission L (entry e) w n := by
  intro admitted
  exact invalid e admitted.entry.valid

#print axioms snapshot
#print axioms sizes
#print axioms owned
#print axioms invalid
#print axioms no_admission
end AspisR1.ARV_Poison
end
