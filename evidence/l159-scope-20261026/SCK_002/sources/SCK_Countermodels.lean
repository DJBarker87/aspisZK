import SCJ_Projection
import SCJ_OrderObstruction
import SCI_SameWorld
import SCH_OracleQuantifier
set_option autoImplicit false
namespace AspisR1.SCK_Countermodels
/-- Minimal two-world/two-entry association countermodel. A genuine same-entry
persistence law holds everywhere and the supplied game holds in its fixed
world. Neither identifies the independently selected accepted run. This is a
quantifier countermodel, NOT a full deployed cryptographic counterexample. -/
theorem fixed_game_not_world_factory :
    ∃ (entry : Bool → Bool) (saved loaded : Bool → Nat) (accept : Bool → Prop),
      entry false = false ∧ saved false = 0 ∧ loaded false = saved false ∧
      (∀ world, entry world = false → loaded world = saved world) ∧
      (∀ world, accept world) ∧
      ∃ world, accept world ∧ loaded world ≠ saved world := by
  refine ⟨id,fun _ => 0,(fun w => if w then 1 else 0),fun _ => True,
    rfl,rfl,rfl,?_,fun _ => True.intro,true,True.intro,?_⟩
  · intro world same
    cases world <;> simp_all
  · decide

/-- Acceptance guards alone do not fix the association error in the tiny model. -/
theorem same_entry_is_material :
    ¬ (∀ (entry : Bool → Bool) (loaded saved : Bool → Nat),
      (∀ w, entry w = false → loaded w = saved w) →
      (∀ w, loaded w = saved w)) := by
  intro every
  have impossible := every id (fun w => if w then 1 else 0) (fun _ => 0)
    (by intro w h; cases w <;> simp_all) true
  exact Nat.noConfusion impossible

/-- Exact released collision-event countermodel, with no new event definition. -/
theorem sublist_event_refuted (Q : Nat) := SCJ_Projection.event_implies_refuted Q

/-- The violated first-occurrence-order property of that same three-read shape. -/
theorem first_order_refuted := SCJ_OrderObstruction.sublist_not_first_order

/-- Actual P1 blocks unguarded universalization of a fixed native world. -/
theorem fixed_native_not_all_worlds := SCH_OracleQuantifier.not_all_worlds

#print axioms fixed_game_not_world_factory
#print axioms same_entry_is_material
#print axioms sublist_event_refuted
#print axioms first_order_refuted
#print axioms fixed_native_not_all_worlds
end AspisR1.SCK_Countermodels
