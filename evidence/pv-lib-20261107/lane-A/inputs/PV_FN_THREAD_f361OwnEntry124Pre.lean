import PV_FN_THREAD_f361OwnEntryProgress
import PV_THR2_Packet12801Issue
set_option autoImplicit false
noncomputable section
namespace PV_FN_THREAD_f361OwnEntry124Pre
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_EVHB_OwnerMachine PV_FN_THREAD_f361 PV_FN_THREAD_f361OwnEntry
open PV_FN_THREAD_f361OwnEntryProgress PV_FN_THREAD_f361JoinStatements

/-- Source12801's actual operand-issued descriptor. -/
def call (x : Input) (s : Store Data) (payload : Data) : PV_W1_LeafBoundary.Entry :=
  ⟨PV_THR2_Packet124CallData.moved s x.a,x.a,x.parent :: x.parents,[],
    PV_THR2_F361.live.body.drop 59,PV_FN_THREAD_f361Call124.fn,[payload],17,x.stack⟩

/-- Derive the literal provider Pre at the actual minted activation. It has
no read/receiver/alias condition and no constructor outcome assumption. -/
theorem provider_pre (x : Input) (pre : Pre x) (s : Store Data) (w : OWNER)
    (es : List PV_RJ4IDB.NativeEvent) (payload : Data)
    (owner : PV_FN_THREAD_OwnerWellFormed.OwnerWellFormed w s.nextActivation)
    (age : x.a < s.nextActivation) :
    PV_FN_THREAD_f124.Pre (input124 x (call x s payload) w es) := by
  let y := input124 x (call x s payload) w es
  have next : y.s.nextActivation = s.nextActivation+1 := by
    exact PV_FN_THREAD_OwnerWellFormed.arguments_next
      {PV_THR2_Packet124CallData.moved s x.a with nextActivation := s.nextActivation+1}
      s.nextActivation [payload] 1
  have activation : y.a = s.nextActivation := rfl
  refine {
    packetCell := ?_
    fresh := ?_
    saved := rfl
    action := rfl
    callers := ?_
    suspended := ?_
    owner := ?_ }
  · change (PV_STX2_Native.arguments s.nextActivation [payload] 1
      {PV_THR2_Packet124CallData.moved s x.a with nextActivation := s.nextActivation+1}).cells
        ⟨s.nextActivation,1,[]⟩ = some payload
    exact write_same _ _ _
  · rw [next,activation]
    omega
  · intro f member
    rw [next]
    change f ∈ (PV_W1_LeafBoundary.pending (call x s payload)).frame ::
      (x.parent :: x.parents) at member
    rcases List.mem_cons.mp member with same | old
    · subst f
      change x.a < s.nextActivation+1
      omega
    · exact Nat.lt_trans (pre.callers f old) (by omega)
  · intro c member f frame
    rw [next]
    exact Nat.lt_trans (pre.suspended c member f frame) (by omega)
  · rw [next]
    exact PV_W1_OwnerWellFormed.counter_mono _ _ _
      ⟨owner.identities,owner.activations⟩ (Nat.le_succ _)

/-- Successful local binding establishes a real cell regardless of its
arbitrary payload. This is source-store validity, not a typed-value premise. -/
theorem bind_value (B : Carrier OWNER Data) (s : Store Data) (w : OWNER)
    (a slot : Nat) (expr : Expr) (t : Store Data)
    (written : PV_STX2_Store.bind B s w a (.local slot) expr = some t) :
    ∃ value, t.cells ⟨a,slot,[]⟩ = some value := by
  cases evaluated : evaluate B s w a expr with
  | none => simp [PV_STX2_Store.bind,evaluated] at written
  | some pair =>
    rcases pair with ⟨value,u⟩
    simp [PV_STX2_Store.bind,evaluated,locate,writeAddress] at written
    subst t
    exact ⟨value,write_same _ _ _⟩

/-- Both original and aggregate-completion binding branches establish the
same local-cell property, without assuming which branch succeeds. -/
theorem bound_value (B : Carrier OWNER Data) (s : Store Data) (w : OWNER)
    (a slot : Nat) (expr : Expr) (t : Store Data)
    (written : PV_THR2_IntrinsicFrameChain.bound B s a (.local slot) expr w = some t) :
    ∃ value, t.cells ⟨a,slot,[]⟩ = some value := by
  unfold PV_THR2_IntrinsicFrameChain.bound at written
  cases original : PV_STX2_Store.bind B s w a (.local slot) expr with
  | none =>
    simp only [original,Option.orElse_none] at written
    exact bind_value _ _ _ _ _ _ _ written
  | some u =>
    simp only [original,Option.orElse_some,Option.some.injEq] at written
    subst t
    exact bind_value _ _ _ _ _ _ _ original

#print axioms provider_pre
#print axioms bind_value
#print axioms bound_value
end PV_FN_THREAD_f361OwnEntry124Pre
