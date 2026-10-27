import R1Z.PV_OptB_Charged
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_OptB_OffPole
open R0P R0Z R0Z.JointView R0Z.FsStatement R0Z.FsAbort R0Z.HvzkV
attribute [local instance] Classical.propDecidable
variable {K CommitHandle Aux Bat Adv : Type} [Field K] [Fintype K] [DecidableEq K]
  [Algebra (ZMod AspisCircleGroupOrder.P) K]
variable (h : HonestProver K) (P : Challenges K → Prop)
  (V : Challenges K → h.Instance → Prop)
  (ab : AbortBridge K CommitHandle Aux Bat Adv) (adv : Adv)
  (x : Statement K CommitHandle) (w : h.Instance) (c : Fin ab.N → ab.Coins)
theorem valid_at_public (good : ¬ poleBad P h V ab adv x w c)
    (k : Fin ab.N) (hPublic : P (ab.draw adv x (c k))) : V (ab.draw adv x (c k)) w := by
  by_contra invalid
  exact good ⟨k, hPublic, invalid⟩

#print axioms valid_at_public
theorem accept_iff_public (good : ¬ poleBad P h V ab adv x w c)
    (k : Fin ab.N) :
    (P (ab.draw adv x (c k)) ∧ V (ab.draw adv x (c k)) w) ↔ P (ab.draw adv x (c k)) :=
  ⟨And.left, fun hp => ⟨hp, valid_at_public h P V ab adv x w c good k hp⟩⟩

#print axioms accept_iff_public
theorem rejected_iff_public (good : ¬ poleBad P h V ab adv x w c)
    (k : Fin ab.N) :
    ¬ (P (ab.draw adv x (c k)) ∧ V (ab.draw adv x (c k)) w) ↔ ¬ P (ab.draw adv x (c k)) := by
  exact not_congr (accept_iff_public h P V ab adv x w c good k)

#print axioms rejected_iff_public
theorem first_good_public (good : ¬ poleBad P h V ab adv x w c) :
    firstGood (fun coin => P (ab.draw adv x coin) ∧ V (ab.draw adv x coin) w) c =
      firstGood (fun coin => P (ab.draw adv x coin)) c :=
  firstGood_congr _ _ c (accept_iff_public h P V ab adv x w c good)

#print axioms first_good_public
theorem first_good_pair (u : h.Instance)
    (hw : ¬ poleBad P h V ab adv x w c) (hu : ¬ poleBad P h V ab adv x u c) :
    firstGood (fun coin => P (ab.draw adv x coin) ∧ V (ab.draw adv x coin) w) c =
      firstGood (fun coin => P (ab.draw adv x coin) ∧ V (ab.draw adv x coin) u) c := by
  rw [first_good_public h P V ab adv x w c hw, first_good_public h P V ab adv x u c hu]

#print axioms first_good_pair
theorem selected_valid (good : ¬ poleBad P h V ab adv x w c)
    (k : Fin ab.N) (selected : firstGood (fun coin => P (ab.draw adv x coin)) c = some k) :
    V (ab.draw adv x (c k)) w :=
  valid_at_public h P V ab adv x w c good k (firstGood_spec _ c k selected)

#print axioms selected_valid
theorem public_none_implies_none (good : ¬ poleBad P h V ab adv x w c)
    (no_public : firstGood (fun coin => P (ab.draw adv x coin)) c = none) :
    firstGood (fun coin => P (ab.draw adv x coin) ∧ V (ab.draw adv x coin) w) c = none := by
  rw [first_good_public h P V ab adv x w c good, no_public]

#print axioms public_none_implies_none
theorem public_some_implies_some (good : ¬ poleBad P h V ab adv x w c)
    (k : Fin ab.N) (selected : firstGood (fun coin => P (ab.draw adv x coin)) c = some k) :
    firstGood (fun coin => P (ab.draw adv x coin) ∧ V (ab.draw adv x coin) w) c = some k := by
  rw [first_good_public h P V ab adv x w c good, selected]

#print axioms public_some_implies_some
theorem public_reject_survives (k : Fin ab.N) (hp : ¬ P (ab.draw adv x (c k))) :
    ¬ (P (ab.draw adv x (c k)) ∧ V (ab.draw adv x (c k)) w) := fun hv => hp hv.1

#print axioms public_reject_survives
theorem earlier_public_rejected (k j : Fin ab.N)
    (selected : firstGood (fun coin => P (ab.draw adv x coin)) c = some k) (before : j < k) :
    ¬ P (ab.draw adv x (c j)) := by
  intro hp
  have least := firstGood_least _ c k selected j hp
  exact (not_le_of_gt before) least

#print axioms earlier_public_rejected
theorem first_good_signal_pair {Event : Type} (u : h.Instance)
    (hw : ¬ poleBad P h V ab adv x w c) (hu : ¬ poleBad P h V ab adv x u c)
    (decode : Option (Fin ab.N) → Option Event) :
    decode (firstGood (fun coin => P (ab.draw adv x coin) ∧ V (ab.draw adv x coin) w) c) =
      decode (firstGood (fun coin => P (ab.draw adv x coin) ∧ V (ab.draw adv x coin) u) c) :=
  congrArg decode (first_good_pair h P V ab adv x w c u hw hu)

#print axioms first_good_signal_pair
end R1Z.PV_OptB_OffPole
