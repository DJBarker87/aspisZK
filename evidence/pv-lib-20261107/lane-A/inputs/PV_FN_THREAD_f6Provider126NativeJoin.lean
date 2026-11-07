import PV_FN_THREAD_f6Provider126Entry
import PV_THR2_PointerIdentityReply
set_option autoImplicit false
noncomputable section
namespace PV_FN_THREAD_f6Provider126NativeJoin
open Aeneas Aeneas.Std PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_EVHB_OwnerMachine PV_FN_THREAD_f126_ReturnedStage
abbrev Backend := PV_W1_OwnerNativeFrame.Backend

/-- Installing the emitted126/222 table and opaque320 disposition twice is
identical on EVERY token. This is a symbolic resolver calculation. -/
theorem table_idempotent (P : Data → Option PV_STX2_SliceSyntax.Program) :
    PV_THR2_PacketDataTable.resolve (PV_THR2_PacketInner320.resolve
      (PV_THR2_PacketDataTable.resolve (PV_THR2_PacketInner320.resolve P))) =
    PV_THR2_PacketDataTable.resolve (PV_THR2_PacketInner320.resolve P) := by
  funext fn
  unfold PV_THR2_PacketDataTable.resolve PV_THR2_PacketInner320.resolve
  cases h : PV_THR2_OffPath.functionId fn with
  | none => simp only [h]
  | some id =>
    by_cases h126 : id = 126
    · subst id; rfl
    · by_cases h222 : id = 222
      · subst id; rfl
      · by_cases h320 : id = 320
        · subst id; rfl
        · simp [h,h126,h222,h320]

/-- At the actual320 request, the provider's installed handler IS W1's
full-reply primitive interpretation on the actual source-issued store.
Neither an answer nor a receiver/read equality is a hypothesis. -/
theorem primitive_at320 {E : Type} (x : Input E) (H : Backend E) (arc : Address) :
    let y := childInput x arc
    let B := PV_THR2_OwnInitExactReturnedCases.carrier x.C x.b
    (PV_FN_THREAD_f126.installed x H arc).H
      (.child PV_THR2_PacketInner320.fn y.s.nextActivation [PV_FN_THREAD_f222_ReturnedStage.receiver y]) y.w =
    (PV_W1_F320.call B (PV_FN_THREAD_f222_EntryOwned.callStore y)
      (PV_THR2_OwnUniformResourceHandler.lift H) y.w y.s.nextActivation (PV_FN_THREAD_f222_ReturnedStage.receiver y)).2 := by
  simp only [PV_FN_THREAD_f126.installed,PV_FN_THREAD_f126_Other.child,
    PV_FN_THREAD_f222.installed,PV_FN_THREAD_f222_EntryOwned.installed,
    PV_FN_THREAD_f222_EntryOwned.handler,ite_true]
  rfl

/-- Entry-owned data, forwarded through CLOSED126's named child Pre theorem,
supplies the primitive value. The complete full reply is retained on every
non-Ok branch, including its exact world and event suffix. -/
theorem reply_at320 {E : Type} (x : Input E) (H : Backend E) (arc p : Address)
    (pre : PV_FN_THREAD_f126.Pre x arc p) :
    let y := childInput x arc
    (PV_FN_THREAD_f126.installed x H arc).H
      (.child PV_THR2_PacketInner320.fn y.s.nextActivation [PV_FN_THREAD_f222_ReturnedStage.receiver y]) y.w =
    PV_THR2_PointerIdentityReply.finish (PV_STX2_TypedReferences.reference p .null) y.w
      (PV_THR2_OwnUniformResourceHandler.lift H
        (.child PV_THR2_PacketInner320.fn y.s.nextActivation [PV_FN_THREAD_f222_ReturnedStage.receiver y]) y.w) := by
  exact PV_FN_THREAD_f222_EntryOwned.reply (childInput x arc) H p
    (PV_FN_THREAD_f126_EntryOwned.child_pre x arc p pre)

/-- No ordinary fallback equality can replace the documented primitive join:
a raw successful null answer differs from the initialized reference computed
from entry ownership. This is an interface diagnostic, not a source failure. -/
theorem raw_success_not_agreement {E : Type} (x : Input E) (H : Backend E) (arc p : Address)
    (pre : PV_FN_THREAD_f126.Pre x arc p)
    (raw : (PV_THR2_OwnUniformResourceHandler.lift H
      (.child PV_THR2_PacketInner320.fn (childInput x arc).s.nextActivation
        [PV_FN_THREAD_f222_ReturnedStage.receiver (childInput x arc)]) (childInput x arc).w).answer = .returned (.ok .null)) :
    (PV_FN_THREAD_f126.installed x H arc).H
      (.child PV_THR2_PacketInner320.fn (childInput x arc).s.nextActivation
        [PV_FN_THREAD_f222_ReturnedStage.receiver (childInput x arc)]) (childInput x arc).w ≠
    PV_THR2_OwnUniformResourceHandler.lift H
      (.child PV_THR2_PacketInner320.fn (childInput x arc).s.nextActivation
        [PV_FN_THREAD_f222_ReturnedStage.receiver (childInput x arc)]) (childInput x arc).w := by
  rw [reply_at320 x H arc p pre]
  rw [PV_THR2_PointerIdentityReply.returned _ .null _ _ raw]
  intro eq
  have bad := congrArg Reply.answer eq
  rw [raw] at bad
  cases bad

#print axioms table_idempotent
#print axioms primitive_at320
#print axioms reply_at320
#print axioms raw_success_not_agreement
end PV_FN_THREAD_f6Provider126NativeJoin
