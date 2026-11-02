import R1Z.PV_V263_GrantControl
/-! Resource success for source item/family control. The bounded callback law
is a component hypothesis, never an extra privacy or Nonempty P premise. -/
set_option autoImplicit false
namespace R1Z.PV_V263_GrantItems
open Aeneas Aeneas.Std PV_V263_World PV_V263_WorkerRequests PV_V263_WorkerControl
open PV_V263_GrantControl
open PV_RJ4IDB (Bytes)
variable {S A : Type}
variable (osCodec : {B : Type} → Request B → Bytes)
variable (vecCodec : PV_V263_MapSpine.VecCall → Bytes)
variable (layouts : PV_V263_MapSpine.Layouts) (n : Nat) (callback : Nat → Q S A)

/-- The law concerns only the source's actual interval; arbitrary callbacks
outside it do not have to terminate. -/
def CallbackLaw : Prop := ∀ i, i < n → Total (callback i)

theorem items_total (k : Nat) (hk : k < 16) (law : CallbackLaw n callback) :
    Total (PV_V263_SourceSpine.items (resourceWorld osCodec vecCodec) layouts n k callback) := by
  apply bind_total _ _ (vector_total osCodec vecCodec _)
  intro unit w
  obtain ⟨values,h⟩ := PV_V263_Family.traverse_total_on
    (PV_V263_SourceItems.step (resourceWorld osCodec vecCodec) layouts n k callback)
    (PV_V263_Family.indices n k) (fun i hi => by
      have cb := law i (PV_V263_Family.in_range n k i hk hi)
      have stepTotal : Total (PV_V263_SourceItems.step
          (resourceWorld osCodec vecCodec) layouts n k callback i) := by
        apply bind_total _ _ cb
        intro a
        apply bind_total _ _ (vector_total osCodec vecCodec _)
        intro unit
        exact pure_returns _ a trivial
      intro v
      obtain ⟨a,ha,_⟩ := stepTotal v
      exact ⟨a,ha⟩) w
  exact ⟨values,h,trivial⟩

theorem family_total (k : Nat) (hk : k < 16) (law : CallbackLaw n callback) :
    Total (PV_V263_SourceSpine.family (resourceWorld osCodec vecCodec) layouts n k callback) := by
  apply bind_total _ _ (vector_total osCodec vecCodec _)
  intro unit
  apply bind_total _ _ (items_total osCodec vecCodec layouts n callback k hk law)
  intro values
  exact pure_returns _ [(values,values.length)] trivial

theorem caught_family (k : Nat) (hk : k < 16) (law : CallbackLaw n callback) :
    Returns (fun caught => ∃ values, caught = Except.ok values)
      (PV_V263_SourceSpine.caughtFamily (resourceWorld osCodec vecCodec) layouts n k callback) :=
  active_returns osCodec .abort k _ _
    (caught_returns .abort _ (family_total osCodec vecCodec layouts n callback k hk law))

#print axioms CallbackLaw
#print axioms items_total
#print axioms family_total
#print axioms caught_family
end R1Z.PV_V263_GrantItems
