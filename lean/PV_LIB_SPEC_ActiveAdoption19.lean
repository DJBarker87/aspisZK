import PV_LIB_A_ActivePrefix17
import PV_LIB_A_ActiveFrames17
import PV_LIB_A_ActiveAgreement17
import PV_LIB_SPEC_ValuesPrefix18
set_option autoImplicit false
noncomputable section
namespace PV_LIB_SPEC_ActiveAdoption19
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_EVHB_OwnerMachine PV_LIB_SPEC_D984 PV_LIB_SPEC_Frozen
open PV_LIB_SPEC_ResourceHistory (Execution Context)
open PV_LIB_SPEC_EntryWorld18 (Entry)

/-- SPEC-C18: adopted successor, retaining the exact v2 resolver, resource
schedule and complete physical entry. Only the diagnosed Adt56 boundary changes. -/
abbrev step := PV_LIB_A_ActiveEnvironment17.step
abbrev history := PV_LIB_A_ActivePrefix17.history

/-- Full Execution transport, not an equality of observations or return values. -/
theorem preserved (entry : Entry) (activation n : Nat) (bound : n ≤ 141) :
    history entry activation n = PV_LIB_SPEC_History18.history entry activation n :=
  PV_LIB_A_ActivePrefix17.preserved entry activation n bound

theorem original85 (entry : Entry) (activation : Nat) :
    history entry activation 85 = PV_LIB_SPEC_World18_Tls85Data16.at85 entry :=
  PV_LIB_A_ActivePrefix17.original85 entry activation

theorem original141 (entry : Entry) (activation : Nat) :
    (history entry activation 141).state = PV_LIB_A_F5FullEntry16.at141 entry :=
  PV_LIB_A_ActivePrefix17.original141 entry activation

theorem world85 (entry : Entry) (activation : Nat) :
    (history entry activation 85).state.current.world = entry.world := by
  rw [preserved entry activation 85 (by decide)]
  exact PV_LIB_SPEC_History18.world85 entry activation

theorem replies85 (entry : Entry) (activation : Nat) :
    (history entry activation 85).consumed =
      [PV_LIB_SPEC_Tls85Data16.origin,PV_LIB_SPEC_Tls68Data16.origin,
       PV_LIB_SPEC_Tls64Data16.origin,PV_LIB_SPEC_Tls59Data15.origin,PV_LIB_SPEC_TlsAt55.origin] := by
  rw [preserved entry activation 85 (by decide)]
  exact PV_LIB_SPEC_History18.replies85 entry activation

/-- Existing Values exclusion transported by name; no Values repair is hidden
inside adoption, and there is no claim about the unknown later suffix. -/
theorem values_prefix (entry : Entry) (activation n : Nat) (bound : n ≤ 85)
    (ctx : Context) (member : ctx ∈ (history entry activation n).consumed) :
    PV_LIB_SPEC_ValuesPrefix18.NoWriter ctx.request := by
  rw [preserved entry activation n (by omega)] at member
  exact PV_LIB_SPEC_ValuesPrefix18.prefix_absent entry activation n bound ctx member

/-- Arbitrary old history predicates retain their exact quantifiers and full
Execution fields through141. Later histories require new successor statements. -/
theorem predicate_prefix (entry : Entry) (activation n : Nat) (bound : n ≤ 141)
    (P : Execution → Prop) :
    P (history entry activation n) ↔ P (PV_LIB_SPEC_History18.history entry activation n) := by
  rw [preserved entry activation n bound]

#print axioms step
#print axioms history
#print axioms preserved
#print axioms original85
#print axioms original141
#print axioms world85
#print axioms replies85
#print axioms values_prefix
#print axioms predicate_prefix
end PV_LIB_SPEC_ActiveAdoption19
