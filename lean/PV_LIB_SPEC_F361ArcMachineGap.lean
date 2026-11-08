import PV_LIB_SPEC_F361Contract
import PV_FN_THREAD_f361CloneFrame
set_option autoImplicit false
noncomputable section
namespace PV_LIB_SPEC_F361ArcMachineGap
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_EVHB_OwnerMachine PV_EVHB_OwnerHeap
abbrev Event := PV_RJ4IDB.NativeEvent
abbrev State := PV_THR2_IntrinsicState.State OWNER Event
abbrev Machine := PV_LIB_SPEC_ThreadMachine.Machine

/-- Actual source12950 descriptor, argument &local17, return local23 and
actual source continuation. The operand move into this issued poll has already
occurred; no original-entry reachability claim is made. -/
def before (s : Store Data) (a : Nat) (parents : List Frame)
    (w : OWNER) (es : List Event) (stack : List Config) : State :=
  ⟨⟨.running (PV_THR2_IntrinsicFrameEnter.pending s a parents []
    (PV_THR2_F361.live.body.drop 64) PV_THR2_Source361PacketChildren.fn63
    [PV_STX2_TypedReferences.reference ⟨a,17,[]⟩ .null] 23),w,es⟩,stack⟩

/-- The D981 machine has no source-effect action for the native Arc clone.
This equality covers its complete native reply; it is not a row proof. -/
theorem native_poll (m : Machine) (s : Store Data) (a : Nat)
    (parents : List Frame) (w : OWNER) (es : List Event) (stack : List Config)
    (leaf : m.programs PV_THR2_Source361PacketChildren.fn63 = none) :
    PV_LIB_SPEC_ThreadMachine.step m (before s a parents w es stack) =
      PV_THR2_IntrinsicFrameFull.received m.carrier s a parents []
        (PV_THR2_F361.live.body.drop 64) PV_THR2_Source361PacketChildren.fn63
        [PV_STX2_TypedReferences.reference ⟨a,17,[]⟩ .null] 23
        (m.handler (.child PV_THR2_Source361PacketChildren.fn63 s.nextActivation
          [PV_STX2_TypedReferences.reference ⟨a,17,[]⟩ .null]) w) es stack := by
  have neutral : PV_THR2_SourceStoreNative.select m.programs
      (PV_THR2_IntrinsicFrameEnter.pending s a parents []
        (PV_THR2_F361.live.body.drop 64) PV_THR2_Source361PacketChildren.fn63
        [PV_STX2_TypedReferences.reference ⟨a,17,[]⟩ .null] 23) = none := by
    change (match m.programs PV_THR2_Source361PacketChildren.fn63 with
      | some _ => none
      | none => none) = none
    cases m.programs PV_THR2_Source361PacketChildren.fn63 <;> rfl
  rw [PV_LIB_SPEC_ThreadMachine.away m _ (by
    intro c status
    cases status
    exact neutral)]
  change PV_THR2_OwnUniformBindings.step m.carrier m.control m.programs m.handler
    (before s a parents w es stack) = _
  have run := PV_THR2_IntrinsicFrameFull.run m.carrier m.control m.programs m.handler
    s a parents [] (PV_THR2_F361.live.body.drop 64)
    PV_THR2_Source361PacketChildren.fn63
    [PV_STX2_TypedReferences.reference ⟨a,17,[]⟩ .null] 23 w es stack rfl leaf
  change PV_THR2_IntrinsicState.step m.carrier m.control m.programs m.handler
    (before s a parents w es stack) = _ at run
  unfold PV_THR2_OwnUniformBindings.step
  rw [run]
  simp only [before]
  split
  · next c d hc hd =>
      cases hc
      rfl
  · rfl

/-- Successful delivery writes arguments/return slots only. The older ArcInner
strong-count cell remains unchanged, regardless of the chosen full reply. -/
theorem count_unchanged (m : Machine) (s : Store Data) (a : Nat)
    (parents : List Frame) (w : OWNER) (es : List Event) (stack : List Config)
    (leaf : m.programs PV_THR2_Source361PacketChildren.fn63 = none)
    (result : Data)
    (returned : (m.handler (.child PV_THR2_Source361PacketChildren.fn63 s.nextActivation
      [PV_STX2_TypedReferences.reference ⟨a,17,[]⟩ .null]) w).answer = .returned (.ok result))
    (inner : Address) (older : inner.activation < a) (issued : a < s.nextActivation) :
    readAddress m.carrier
      (PV_W1_LeafBoundary.statusStore
        (PV_LIB_SPEC_ThreadMachine.step m (before s a parents w es stack)).current.status)
      (PV_THR2_LibrarySemantics_ArcClone.countAddress inner) =
    readAddress m.carrier s (PV_THR2_LibrarySemantics_ArcClone.countAddress inner) := by
  rw [native_poll m s a parents w es stack leaf]
  let r := m.handler (.child PV_THR2_Source361PacketChildren.fn63 s.nextActivation
    [PV_STX2_TypedReferences.reference ⟨a,17,[]⟩ .null]) w
  have replyEq : r = ⟨.returned (.ok result),r.world,r.events⟩ := by
    cases hr : r with
    | mk ans world events =>
      have eq : ans = .returned (.ok result) := by
        simpa only [hr] using (show r.answer = .returned (.ok result) from returned)
      cases eq
      rfl
  change readAddress m.carrier
    (PV_W1_LeafBoundary.statusStore
      (PV_THR2_IntrinsicFrameFull.received m.carrier s a parents []
        (PV_THR2_F361.live.body.drop 64) PV_THR2_Source361PacketChildren.fn63
        [PV_STX2_TypedReferences.reference ⟨a,17,[]⟩ .null] 23 r es stack).current.status)
    _ = _
  rw [replyEq]
  rw [PV_THR2_FrameFullReturned.received]
  simp only [PV_W1_LeafBoundary.statusStore]
  unfold readAddress PV_THR2_StaticReply.returnedStore
  have notCaller : inner.activation ≠ a := Nat.ne_of_lt older
  have notNative : inner.activation ≠ s.nextActivation :=
    Nat.ne_of_lt (Nat.lt_trans older issued)
  dsimp only [PV_THR2_LibrarySemantics_ArcClone.countAddress,write,
    PV_THR2_StaticCall.issued,PV_STX2_Native.arguments]
  simp only [show (⟨inner.activation,inner.localIndex,[]⟩ : Address) ≠ ⟨a,23,[]⟩ from
      fun h => notCaller (congrArg Address.activation h),
    show (⟨inner.activation,inner.localIndex,[]⟩ : Address) ≠ ⟨s.nextActivation,0,[]⟩ from
      fun h => notNative (congrArg Address.activation h),
    show (⟨inner.activation,inner.localIndex,[]⟩ : Address) ≠ ⟨s.nextActivation,1,[]⟩ from
      fun h => notNative (congrArg Address.activation h),if_false]

/-- Exact forbidden pair at12950: D981 native delivery plus the documented
successful Arc::clone increment cannot both describe this same source cell.
This is local, NOT a contradiction of the full OwnInit joint premises. -/
theorem increment_impossible (m : Machine) (s : Store Data) (a : Nat)
    (parents : List Frame) (w : OWNER) (es : List Event) (stack : List Config)
    (leaf : m.programs PV_THR2_Source361PacketChildren.fn63 = none)
    (result : Data)
    (returned : (m.handler (.child PV_THR2_Source361PacketChildren.fn63 s.nextActivation
      [PV_STX2_TypedReferences.reference ⟨a,17,[]⟩ .null]) w).answer = .returned (.ok result))
    (inner : Address) (older : inner.activation < a) (issued : a < s.nextActivation)
    (count : Nat)
    (initialized : readAddress m.carrier s
      (PV_THR2_LibrarySemantics_ArcClone.countAddress inner) = some (.number count)) :
    readAddress m.carrier
      (PV_W1_LeafBoundary.statusStore
        (PV_LIB_SPEC_ThreadMachine.step m (before s a parents w es stack)).current.status)
      (PV_THR2_LibrarySemantics_ArcClone.countAddress inner) ≠ some (.number (count+1)) := by
  rw [count_unchanged m s a parents w es stack leaf result returned inner older issued,
    initialized]
  intro eq
  have same : count = count+1 := Data.number.inj (Option.some.inj eq)
  omega

#print axioms before
#print axioms native_poll
#print axioms count_unchanged
#print axioms increment_impossible
end PV_LIB_SPEC_F361ArcMachineGap
