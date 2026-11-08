import PV_LIB_SPEC_AssemblyEnvironment14
set_option autoImplicit false
noncomputable section
namespace PV_LIB_SPEC_RawVec14
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_EVHB_OwnerMachine PV_LIB_SPEC_D984 PV_LIB_SPEC_Frozen
/-- The FULL program table expands164, so its actual native constructor is
268 at7894. A164 reply adapter alone cannot unblock this source prefix.
These source tags are retained generic359 emission, not an invented concrete
monomorphized type tag or a change to the resolver. -/
def token : Data := PV_THR2_SourceRawTable.fn268
def rawKind : Data := match PV_THR2_F359.node44 with
  | .leaf (.aggregateMove _ _ kind _) => kind | _ => .null
def markerKind : Data := match PV_THR2_F359.node43 with
  | .leaf (.aggregateMove _ _ kind _) => kind | _ => .null
def inner : Data := PV_THR2_KeyValues.pack PV_LIB_SPEC_VectorKinds14.innerKind
  [.number 8,.number 0,.null]
def value : Data := PV_THR2_KeyValues.pack rawKind
  [inner,PV_THR2_KeyValues.pack markerKind []]
def reply (w : OWNER) (r : Reply OWNER Event Data) : Reply OWNER Event Data :=
  match r.answer with
  | .returned (.ok _) => ⟨.returned (.ok value),w,[]⟩
  | _ => r

theorem dispatch :
    PV_LIB_SPEC_Full.programs PV_LIB_SPEC_PreludeValues14.fn164 = some PV_THR2_F164.live ∧
    PV_LIB_SPEC_Full.programs token = none := ⟨rfl,rfl⟩
theorem fields (p : Parameters) :
    (runtime p).carrier.field value 0 = some inner ∧
    (runtime p).carrier.field inner 0 = some (.number 8) ∧
    (runtime p).carrier.field inner 1 = some (.number 0) := ⟨rfl,rfl,rfl⟩

#print axioms token
#print axioms rawKind
#print axioms markerKind
#print axioms inner
#print axioms value
#print axioms reply
#print axioms dispatch
#print axioms fields
end PV_LIB_SPEC_RawVec14
