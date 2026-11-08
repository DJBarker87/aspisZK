import PV_LIB_A_WeakOwnerFree9
set_option autoImplicit false
noncomputable section
namespace PV_LIB_A_WeakFreeAgreement9
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_EVHB_OwnerMachine PV_EVHB_OwnerHeap PV_THR2_SourceStoreLibrary
open PV_LIB_StoreActionTable

/-- Instruction/phase shape only. This is an agreement criterion, not a row
Pre or an assumption that a destructor succeeds or has no source effect. -/
def Neutral (C : Carrier OWNER Data) (K : Control)
    (P : Data → Option PV_STX2_SliceSyntax.Program) (s : SourceState) : Prop :=
  (∀ site p, s.applied = some (site,.deallocate p) → site.action ≠ .weakDrop683) ∧
  (∀ c site, s.base.current.status = .running c → s.applied = none →
    sourceSelect (v2ProvenancePrograms P) c = some site → site.action ≠ .weakDrop683)

/-- ONE symbolic local agreement with the identical OWNER/resources/carrier
base, away from selected Weak calls and their retained free phases. -/
theorem agreement (C : Carrier OWNER Data) (K : Control)
    (P : Data → Option PV_STX2_SliceSyntax.Program) (resources : Resources) (encode : Encode)
    (H : Handler) (values : Values OWNER PV_RJ4IDB.NativeEvent) (s : SourceState)
    (away : Neutral C K P s) :
    PV_LIB_A_WeakOwnerFree9.step C K P resources encode H values s =
      v2ProvenanceStep C K P resources encode H values s := by
  unfold PV_LIB_A_WeakOwnerFree9.step
  cases ha : s.applied with
  | none =>
    cases hs : s.base.current.status <;> try rfl
    rename_i c
    cases hp : sourceSelect (v2ProvenancePrograms P) c with
    | none => simp only [ha,hs,hp]
    | some site =>
      have noWeak := away.2 c site hs ha hp
      cases haction : site.action <;> simp only [ha,hs,hp,haction] <;>
        exact False.elim (noWeak haction)
  | some phase =>
    rcases phase with ⟨site,tail⟩
    cases tail with
    | done => rfl
    | deallocate p =>
      cases hs : s.base.current.status <;> try rfl
      have noWeak := away.1 site p ha
      cases haction : site.action <;> simp only [ha,hs,haction] <;>
        exact False.elim (noWeak haction)

#print axioms Neutral
#print axioms agreement
end PV_LIB_A_WeakFreeAgreement9
