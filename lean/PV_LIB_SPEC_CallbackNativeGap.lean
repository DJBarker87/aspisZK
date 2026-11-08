import PV_LIB_SPEC_CallbackImageGap
import PV_LIB_SPEC_SiteHistory
set_option autoImplicit false
noncomputable section
namespace PV_LIB_SPEC_CallbackNativeGap
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_EVHB_OwnerMachine PV_EVHB_OwnerHeap PV_LIB_SPEC_Frozen PV_LIB_SPEC_D984

def kind : Data := match PV_THR2_F361.node88 with
  | .leaf (.aggregateMove _ _ kind _) => kind | _ => .null

def payload (f hooks packet : Data) : Data := PV_THR2_KeyValues.pack kind [f,hooks,packet]

/-- Discriminate the retained source generic argument without recursively
comparing a large metadata tree. Generic type variables are Deduplicated;
the concrete closure is a HashConsedValue. -/
def typeVariableArgument : Data → Bool
  | .object [("Regular",.object [("kind",_),
      ("generics",.object [("regions",_),
        ("types",.array [.object [("Deduplicated",_)]]),
        ("const_generics",_),("trait_refs",_)])])] => true
  | _ => false

theorem distinct : PV_THR2_Source361BoxTable.fnClosureBoxFull ≠ PV_THR2_Packet124BoxIssue17.fn := by
  intro impossible
  have tags := congrArg typeVariableArgument impossible
  change false = true at tags
  cases tags

theorem arc_away (C : Carrier OWNER Data) (K : Control) (resources : Resources)
    (encode : Encode) (s : Store Data)
    (H : PV_STX2_Native.Request Data → OWNER → Reply OWNER Event Data)
    (f hooks packet : Data) (w : OWNER) :
    PV_LIB_SPEC_SiteArc.handler C K resources encode s H
      (.child PV_THR2_Source361BoxTable.fnClosureBoxFull s.nextActivation [payload f hooks packet]) w =
      some (H (.child PV_THR2_Source361BoxTable.fnClosureBoxFull s.nextActivation [payload f hooks packet]) w) := by
  simp only [PV_LIB_SPEC_SiteArc.handler,payload,PV_THR2_KeyValues.pack,List.map_cons,List.map_nil]
  rw [if_neg (by rintro ⟨same,_,_⟩; exact distinct same)]

/-- The assembled, repaired native interpreter STILL installs the ownership-
only callback reply at the actual13923 token and source closure kind. Native
Environment and all three source captures are arbitrary. No selected reply,
codec success or desired store is postulated. -/
theorem native (p : Parameters) (c : Config) (w : OWNER) (a : Nat) (f hooks packet : Data) :
    PV_LIB_SPEC_SiteRuntime.native p c
      (.child PV_THR2_Source361BoxTable.fnClosureBoxFull a [payload f hooks packet]) w =
      some (PV_THR2_ClosureBoxAllocation.reply p.resources p.encode
        {c.store with nextActivation := a} w) := by
  unfold PV_LIB_SPEC_SiteRuntime.native
  dsimp only
  rw [arc_away,PV_THR2_ClosureBoxActivationHandler.at_call]

/-- Successful local13923 poll data, not an original-entry reachability claim. -/
def parameters (env : Environment) : Parameters :=
  {PV_LIB_SPEC_ConcreteEntry.parameters with
    resources := PV_LIB_SPEC_SuccessResources.callbackResources,environment := env}
def config : Config := ⟨{activation := 1,remaining := PV_THR2_F361.live.body.drop 92},[],
  PV_LIB_SPEC_LocalOwnership.allocationStore⟩

theorem native_memory (env : Environment) (f hooks packet : Data) :
    (PV_LIB_SPEC_SiteRuntime.native (parameters env) config
      (.child PV_THR2_Source361BoxTable.fnClosureBoxFull 10 [payload f hooks packet])
      PV_LIB_SPEC_LocalOwnership.before).map (fun r => r.world.world.memory 8224) = some none := by
  rw [native]
  rfl

/-- CHECKED full native-assembly contradiction at this LOCAL successful poll:
no native schedule can add the missing callback byte suffix in this assembly.
The binary stores offset32 for every stack snapshot and Packet pointer. -/
theorem native_disagrees (env : Environment) (f hooks packet : Data)
    (snapshot : PV_LIB_SPEC_AllocationImages.Memory)
    (rsp packetPointer capturePointer captureLength : Nat) :
    (PV_LIB_SPEC_SiteRuntime.native (parameters env) config
      (.child PV_THR2_Source361BoxTable.fnClosureBoxFull 10 [payload f hooks packet])
      PV_LIB_SPEC_LocalOwnership.before).map (fun r => r.world.world.memory 8224) ≠
      some (PV_LIB_SPEC_AllocationImages.overwrite 8192
        (PV_LIB_SPEC_AllocationImages.callback snapshot rsp packetPointer capturePointer captureLength)
        PV_LIB_SPEC_LocalOwnership.allocated.world.memory 8224) := by
  rw [native_memory,PV_LIB_SPEC_CallbackImageGap.binary_memory]
  intro impossible
  cases impossible

#print axioms kind
#print axioms payload
#print axioms typeVariableArgument
#print axioms distinct
#print axioms arc_away
#print axioms native
#print axioms parameters
#print axioms config
#print axioms native_memory
#print axioms native_disagrees
end PV_LIB_SPEC_CallbackNativeGap
