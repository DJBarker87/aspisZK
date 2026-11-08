import PV_LIB_A_F219To31813
import PV_THR2_Catch219Callbacks
set_option autoImplicit false
noncomputable section
namespace PV_LIB_A_CallbackBindings14
open PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine PV_EVHB_OwnerMachine
open PV_LIB_A_SourceSequence13

theorem unary (C : Carrier OWNER Data) (s : Store Data) (a dest : Nat)
    (w : OWNER) (op token : Data)
    (constant : C.constant token = some token) (cast : C.unary op token = some token) :
    bound C s a (.local dest) (.unary op (.constant token)) w =
      some (write s ⟨a,dest,[]⟩ (some token)) := by
  simp [bound,PV_THR2_IntrinsicFrameChain.bound,PV_STX2_Store.bind,evaluate,operand,
    locate,writeAddress,constant,cast]

theorem callback (C : Carrier OWNER Data) (b catcher : Bool)
    (s : Store Data) (a dest : Nat) (w : OWNER) :
    bound (PV_THR2_EntryDynamic.carrier C b) s a (.local dest)
      (.unary (PV_THR2_Catch219Callbacks.token catcher).1
        (.constant (PV_THR2_Catch219Callbacks.token catcher).2)) w =
      some (write s ⟨a,dest,[]⟩ (some (PV_THR2_Catch219Callbacks.token catcher).2)) :=
  unary _ s a dest w _ _ (PV_THR2_Catch219Callbacks.casts C b catcher).1
    (PV_THR2_Catch219Callbacks.casts C b catcher).2

def unit : Data := .object [("kind",.object [("Adt",.array [.null,.array []])]),
  ("ty",.object [("Deduplicated",.number 646)])]

theorem pointer (C : Carrier OWNER Data) (b : Bool)
    (s : Store Data) (a : Nat) (w : OWNER) :
    bound (PV_THR2_EntryDynamic.carrier C b) s a (.local 7)
      (.rawPointer (.local 2) (.constant unit)) w =
      some (write s ⟨a,7,[]⟩ (some (PV_STX2_TypedReferences.reference ⟨a,2,[]⟩ .null))) := by
  have literal : (PV_THR2_EntryDynamic.carrier C b).constant unit = some .null := rfl
  simp [bound,PV_THR2_IntrinsicFrameChain.bound,PV_STX2_Store.bind,evaluate,operand,
    locate,writeAddress,literal]
  rfl

#print axioms unary
#print axioms callback
#print axioms pointer
end PV_LIB_A_CallbackBindings14
