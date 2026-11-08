import PV_LIB_A_CellDestruct504
import PV_LIB_A_TypedBindingFacts
set_option autoImplicit false
noncomputable section
namespace PV_LIB_A_CellDestructFacts
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_EVHB_OwnerMachine PV_THR2_SourceStoreLibrary
open PV_LIB_A_TypedDestruct PV_LIB_A_CellSetBegin

/-- Source selection follows from the actual typed metadata and receiver/write
projection. The caller does not supply a whole-call Store or success premise. -/
theorem selected_from_source (C : Carrier OWNER Data)
    (P : Data → Option PV_STX2_SliceSyntax.Program) (c : Config) (w : OWNER)
    (wait : PV_STX2_Native.Waiting Data) (fn normalized reference value old : Data)
    (a : Nat) (post : Store Data) (d : Destructor) (resolved : Resolution) (p : Address)
    (completed : c.frame.completed = none) (waiting : c.frame.waiting = some wait)
    (request : wait.request = .child fn a [reference,value])
    (function : PV_THR2_OffPath.functionId fn = some 504) (native : P fn = none)
    (metadata : normalize 64 fn = some normalized)
    (destruct : destructor normalized = some d)
    (meaning : PV_LIB_A_ExactDestructMethods.resolve d.type d.witness = some resolved)
    (received : receiver C c.store w reference = some (p,old))
    (replaced : writeAddress C c.store p (some value) = some post) :
    PV_LIB_A_CellDestruct504.select C P c w = some ⟨wait,a,⟨post,old,d⟩,resolved⟩ := by
  have begun := begin_from_source C c.store post w normalized reference value old d p
    destruct received replaced
  simp [PV_LIB_A_CellDestruct504.select,completed,waiting,request,function,native,
    metadata,begun,meaning]

/-- The actual nontrivial602 specialization is bound, not classified Copy. -/
theorem emitted602 :
    PV_LIB_A_ExactDestructMethods.resolve PV_LIB_A_CellSetMetadata.d602.type
      PV_LIB_A_CellSetMetadata.d602.witness =
      some (.call (fnPtr 608 ⟨[.atom "Erased"],[],[],[]⟩)) := rfl

/-- The saved old T and unit result occupy distinct source cells. -/
theorem saved_old (c : Config) (w : OWNER) (es : List PV_RJ4IDB.NativeEvent)
    (stack : List Config) (selected : PV_LIB_A_CellDestruct504.Site) (unit : Data) :
    ∃ next, (PV_LIB_A_CellDestruct504.enter c w es stack selected unit).base.current.status =
      .running next ∧
      next.store.cells ⟨selected.activation,3,[]⟩ = some selected.prepared.old ∧
      next.store.cells ⟨selected.activation,0,[]⟩ = some unit := by
  refine ⟨_,rfl,?_,?_⟩ <;> simp [PV_LIB_A_CellDestruct504.enter,write]

/-- Source slots belonging to the dropping parent or a prior source allocation
are untouched by the two bookkeeping writes. The replacement's own write is
kept in prepared.store and is not abstracted away. -/
theorem away_holder (c : Config) (w : OWNER) (es : List PV_RJ4IDB.NativeEvent)
    (stack : List Config) (selected : PV_LIB_A_CellDestruct504.Site) (unit : Data)
    (address : Address) (away : address.activation ≠ selected.activation) :
    ∃ next, (PV_LIB_A_CellDestruct504.enter c w es stack selected unit).base.current.status =
      .running next ∧ next.store.cells address = selected.prepared.store.cells address := by
  have a0 : address ≠ (⟨selected.activation,0,[]⟩ : Address) := by
    intro h
    exact away (congrArg Address.activation h)
  have a3 : address ≠ (⟨selected.activation,3,[]⟩ : Address) := by
    intro h
    exact away (congrArg Address.activation h)
  refine ⟨_,rfl,?_⟩
  simp only [PV_LIB_A_CellDestruct504.enter,write,if_neg a0,if_neg a3]

#print axioms selected_from_source
#print axioms emitted602
#print axioms saved_old
#print axioms away_holder
end PV_LIB_A_CellDestructFacts
