import PV_LIB_A_F6History12
import PV_LIB_A_AtomicBoolNewV2
import PV_THR2_LibrarySemantics_AtomicUsizeNew
set_option autoImplicit false
noncomputable section
namespace PV_LIB_A_F6Constructors12
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_EVHB_OwnerMachine PV_W1_LeafBoundary PV_W1_OwnerNativeFrame

/-- Exact1782 source boundary; store.nextActivation is the issued child id. -/
def entry121 (s : Store Data) (a : Nat) (parents : List Frame) (stack : List Config) : Entry :=
  ⟨s,a,parents,[],PV_THR2_F6.live.body.drop 17,PV_THR2_ScopeCall121.fn,[.number 0],5,stack⟩

/-- Exact1874 source boundary, using the state already reached after122. -/
def entry123 (s : Store Data) (a : Nat) (parents : List Frame) (stack : List Config) : Entry :=
  ⟨s,a,parents,[],PV_THR2_F6.live.body.drop 21,PV_THR2_ScopeCall123.fn,[.boolean false],7,stack⟩

/-- The provider's existing named121 fact at the ACTUAL f6 request. This
retains nonreturns and does not choose a constructor payload or world. -/
theorem counter (C : Carrier OWNER Data) (H : Backend PV_RJ4IDB.NativeEvent)
    (s : Store Data) (a : Nat) (parents : List Frame) (stack : List Config)
    (w : OWNER) (changes : Address → Option Data)
    (fact : PV_THR2_LibrarySemantics_AtomicUsizeNew.Fact C (entry121 s a parents stack) H w changes 0)
    (v : Data) (returned : (PV_THR2_ScopeReply121.reply
      (PV_THR2_OwnUniformResourceHandler.lift H) s w).answer = .returned (.ok v)) :
    PV_THR2_LibrarySemantics_AtomicUsizeNew.Holds v 0 ∧
      (PV_THR2_ScopeReply121.reply (PV_THR2_OwnUniformResourceHandler.lift H) s w).world = w := by
  have result := fact v returned
  exact ⟨result.value,result.world⟩

/-- Exact source123 fact provides the numeric AtomicBool byte0, not an invented
boolean byte. Its allocation metadata remains the provider's existential kinds. -/
theorem panicked (H : Backend PV_RJ4IDB.NativeEvent)
    (s : Store Data) (a : Nat) (parents : List Frame) (stack : List Config) (w : OWNER)
    (fact : PV_LIB_A_AtomicBoolNewV2.PV_THR2_LibrarySemantics_AtomicBoolNew123
      (entry123 s a parents stack) H w false)
    (v : Data) (returned : (PV_THR2_ScopeReply123.reply
      (PV_THR2_OwnUniformResourceHandler.lift H) s w).answer = .returned (.ok v)) :
    PV_LIB_A_AtomicBoolNewV2.Holds v false ∧
      (PV_THR2_ScopeReply123.reply (PV_THR2_OwnUniformResourceHandler.lift H) s w).world = w := by
  exact fact v returned

/-- Values are decoded through the SAME named source aggregate interpretation. -/
theorem counter_word (C : Carrier OWNER Data) (b : Bool) (v : Data)
    (held : PV_THR2_LibrarySemantics_AtomicUsizeNew.Holds v 0) :
    readFields (PV_THR2_OwnInitExactReturnedCases.carrier C b) [0,0] v = some (.number 0) :=
  PV_THR2_LibrarySemantics_AtomicUsizeNew.held_value C b v 0 held

theorem panic_word (C : Carrier OWNER Data) (b : Bool) (v : Data)
    (held : PV_LIB_A_AtomicBoolNewV2.Holds v false) :
    readFields (PV_THR2_OwnInitExactReturnedCases.carrier C b) [0,0] v = some (.number 0) :=
  PV_LIB_A_AtomicBoolNewV2.held_byte C b false v held

#print axioms entry121
#print axioms entry123
#print axioms counter
#print axioms panicked
#print axioms counter_word
#print axioms panic_word
end PV_LIB_A_F6Constructors12
