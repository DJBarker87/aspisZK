import PV_LIB_A_CallbackBindings14
import PV_THR2_Catch219CatchPointer
set_option autoImplicit false
noncomputable section
namespace PV_LIB_A_CallbackTail14
open PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine PV_EVHB_OwnerMachine
open PV_LIB_A_SourceSequence13 PV_LIB_A_SequenceFrontier13

def seq : Seq := prepend PV_THR2_F219.node11 (prepend PV_THR2_F219.node12
  (prepend PV_THR2_F219.node13 (prepend PV_THR2_F219.node14 (prepend PV_THR2_F219.node15 .done))))
def stored (s : Store Data) (a : Nat) :=
  PV_THR2_Catch219CatchPointer.afterStore (PV_THR2_Catch219TryPointer.afterStore s a) a

theorem shape : nodes seq ++ PV_THR2_F219.live.body.drop 16 = PV_THR2_F219.live.body.drop 11 := rfl

theorem result (C : Carrier OWNER Data) (b : Bool) (s : Store Data) (a : Nat)
    (parents : List Frame) (loops : List LoopFrame)
    (rest : List PV_STX2_SliceSyntax.Node) (w : OWNER) :
    PV_LIB_A_SourceSequence13.result (PV_THR2_EntryDynamic.carrier C b) a parents loops rest w seq s =
      .running ⟨{activation := a,remaining := rest,loops := loops},parents,stored s a⟩ := by
  change PV_LIB_A_SourceSequence13.result _ a parents loops rest w
    (.bind _ (.local 6) (.unary (PV_THR2_Catch219Callbacks.token false).1
      (.constant (PV_THR2_Catch219Callbacks.token false).2)) _) s = _
  simp only [PV_LIB_A_SourceSequence13.result,PV_LIB_A_CallbackBindings14.callback]
  simp only [prepend,PV_THR2_F219.node12,PV_LIB_A_SourceSequence13.result]
  change PV_LIB_A_SourceSequence13.result _ a parents loops rest w
    (.bind _ (.local 7) (.rawPointer (.local 2) (.constant PV_LIB_A_CallbackBindings14.unit)) _) _ = _
  rw [PV_LIB_A_SourceSequence13.result,PV_LIB_A_CallbackBindings14.pointer]
  change PV_LIB_A_SourceSequence13.result _ a parents loops rest w
    (.storage _ true 8 (.bind _ (.local 8) (.unary (PV_THR2_Catch219Callbacks.token true).1
      (.constant (PV_THR2_Catch219Callbacks.token true).2)) .done)) _ = _
  simp only [PV_LIB_A_SourceSequence13.result,PV_LIB_A_CallbackBindings14.callback]
  rfl

theorem cost (C : Carrier OWNER Data) (b : Bool) (s : Store Data) (a : Nat) (w : OWNER) :
    PV_LIB_A_SourceSequence13.steps (PV_THR2_EntryDynamic.carrier C b) a w seq s = 5 := by
  change PV_LIB_A_SourceSequence13.steps _ a w
    (.bind _ (.local 6) (.unary (PV_THR2_Catch219Callbacks.token false).1
      (.constant (PV_THR2_Catch219Callbacks.token false).2)) _) s = _
  simp only [PV_LIB_A_SourceSequence13.steps,PV_LIB_A_CallbackBindings14.callback]
  simp only [prepend,PV_THR2_F219.node12,PV_LIB_A_SourceSequence13.steps]
  change 1 + (1 + PV_LIB_A_SourceSequence13.steps (PV_THR2_EntryDynamic.carrier C b) a w
    (.bind _ (.local 7) (.rawPointer (.local 2) (.constant PV_LIB_A_CallbackBindings14.unit)) _) _) = 5
  rw [PV_LIB_A_SourceSequence13.steps]
  rw [PV_LIB_A_CallbackBindings14.pointer]
  change 1 + (1 + (1 + PV_LIB_A_SourceSequence13.steps _ a w
    (.storage _ true 8 (.bind _ (.local 8) (.unary (PV_THR2_Catch219Callbacks.token true).1
      (.constant (PV_THR2_Catch219Callbacks.token true).2)) .done)) _)) = 5
  simp only [PV_LIB_A_SourceSequence13.steps,PV_LIB_A_CallbackBindings14.callback]

/-- Readbacks follow from the actual source stores, independently of native134. -/
theorem cells (s : Store Data) (a : Nat) :
    (stored s a).cells ⟨a,6,[]⟩ = some (PV_THR2_Catch219Callbacks.token false).2 ∧
    (stored s a).cells ⟨a,7,[]⟩ = some (PV_STX2_TypedReferences.reference ⟨a,2,[]⟩ .null) ∧
    (stored s a).cells ⟨a,8,[]⟩ = some (PV_THR2_Catch219Callbacks.token true).2 := by
  simp [stored,PV_THR2_Catch219CatchPointer.afterStore,PV_THR2_Catch219TryPointer.afterStore,write]

#print axioms shape
#print axioms result
#print axioms cost
#print axioms cells
end PV_LIB_A_CallbackTail14
