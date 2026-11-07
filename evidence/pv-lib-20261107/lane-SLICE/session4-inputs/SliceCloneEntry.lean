import PV_STX2_SliceColumnBorrow
set_option autoImplicit false
noncomputable section
namespace PV_STX2_SliceCloneEntry
open Aeneas Aeneas.Std ProverRwFull PV_STX_Machine PV_STX2_Syntax PV_STX2_Store
open PV_STX2_SliceSyntax PV_STX2_SliceMachine
open PV_STX2_SliceColumnPointer PV_STX2_SliceColumnBorrow PV_STX2_SliceLoopGuard
open PV_STX2_SliceColumnEntry PV_STX2_SliceDriverBuiltin

/-- Conditional on owner acceptance of the translator patch. The source
LOCAL7 move precedes the f13 activation and actual old-column argument. -/
def cloneStore (s : Store Data) (a index : Nat) : Store Data :=
  let moved := write s ⟨a,7,[]⟩ none
  let child := moved.nextActivation
  PV_STX2_Native.arguments child [oldReference index] 1
    {moved with nextActivation := child+1}
/-- Conditional on owner acceptance of the translator patch. The actual
f6/s154 saved caller retains its complete parents and emitted cleanup. -/
def cloneConfig (s : Store Data) (parents : List Frame) (a index : Nat) : Config :=
  ⟨{activation := s.nextActivation,remaining := PV_STX2_SliceF13.program.body},
    PV_STX2_SliceEntries.F6S154.saved a s.nextActivation (PV_STX2_SliceF6.program.body.drop 15)
      [oldReference index] :: parents,cloneStore s a index⟩
/-- Conditional on owner acceptance of the translator patch. Source f6/s154
uses the derived LOCAL7 operand; no f13 capture is supplied independently. -/
theorem source_entry {W E : Type} (base : Carrier W Data) (control : Control)
    (native : PV_STX2_Native.Request Data → W → Reply W E Data)
    (s : Store Data) (parents : List Frame) (w : W) (a index : Nat)
    (argument : s.cells ⟨a,7,[]⟩ = some (oldReference index)) :
    advance (PV_STX2_SliceArrayInterpretation.carrier (comparisons (one base))) control
      PV_STX2_SlicePrograms.dispatch
      (PV_STX2_SliceArrayInterpretation.handler (PV_STX2_SliceDriverArrays.handler native)) 2
      ⟨.running ⟨{activation := a,remaining := PV_STX2_SliceF6.program.body.drop 14},parents,s⟩,w,[]⟩ =
      ⟨.running (cloneConfig s parents a index),w,[]⟩ := by
  change advance _ _ _ _ 2
    ⟨.running (PV_STX2_SliceEntries.F6S154.caller a (PV_STX2_SliceF6.program.body.drop 15) parents s),w,[]⟩ = _
  rw [PV_STX2_SliceEntries.F6S154.source_call_entry]
  simp [PV_STX2_SliceEntries.F6S154.captures,operands,operand,PV_STX2_Store.read,
    locate,writeAddress,write,argument,cloneConfig,cloneStore]
/-- Conditional on owner acceptance of the translator patch. The first
column captures are derived from the source f8 call's operand moves. -/
theorem first_captures (value : aspis_statement.state_only_trace.StateOnlyTraceFoundation) :
    (firstColumn value).store.cells ⟨11,1,[]⟩ = some PV_STX2_SliceWrappedEntry.columnReference ∧
    (firstColumn value).store.cells ⟨11,2,[]⟩ = some (PV_STX2_SliceLoopCallback.indexTuple 0) := by
  have counter : (PV_STX2_SliceWrappedEntry.wrappedStore
    (PV_STX2_SliceLoopCallback.firstCallback value).store 10 0).nextActivation = 11 := rfl
  simp [firstColumn,columnConfig,columnStore,PV_STX2_Native.arguments,write,counter]
/-- Conditional on owner acceptance of the translator patch. Sixteen source
transitions from the first reached column enter f13 through the saved old
pointer, after mutating the source wrapper in its original driver cell. -/
theorem column_cut {W E : Type} (base : Carrier W Data) (control : Control)
    (native : PV_STX2_Native.Request Data → W → Reply W E Data)
    (value : aspis_statement.state_only_trace.StateOnlyTraceFoundation) (w : W) :
    advance (PV_STX2_SliceArrayInterpretation.carrier (comparisons (one base))) control
      PV_STX2_SlicePrograms.dispatch
      (PV_STX2_SliceArrayInterpretation.handler (PV_STX2_SliceDriverArrays.handler native)) 16
      ⟨.running (firstColumn value),w,[]⟩ =
      ⟨.running (cloneConfig (borrowed (firstColumn value).store 11 0)
        (firstColumn value).callers 11 0),w,[]⟩ := by
  change advance _ _ _ _ 16
    ⟨.running ⟨{activation := 11,remaining := PV_STX2_SliceF6.program.body},
      (firstColumn value).callers,(firstColumn value).store⟩,w,[]⟩ = _
  rw [advance_add _ _ _ _ 14 2,
    source_borrow base control native (firstColumn value).store (firstColumn value).callers w 11 0
      (first_captures value).1 (first_captures value).2 (first_root value) (by decide)]
  apply source_entry
  simp [borrowed,write]
/-- Conditional on owner acceptance of the translator patch. The first
f13 configuration retains every suspended source caller, including f9's loop. -/
def firstClone (value : aspis_statement.state_only_trace.StateOnlyTraceFoundation) : Config :=
  cloneConfig (borrowed (firstColumn value).store 11 0) (firstColumn value).callers 11 0
/-- Conditional on owner acceptance of the translator patch. The actual
initialized Foundation run reaches f13 after 107 source transitions. This
remains a logical value/store prefix, not the missing OWNER/native Vec bridge. -/
theorem initialized_clone {W E : Type} (base : Carrier W Data) (control : Control)
    (native : PV_STX2_Native.Request Data → W → Reply W E Data)
    (value : aspis_statement.state_only_trace.StateOnlyTraceFoundation) (w : W) :
    advance (PV_STX2_SliceArrayInterpretation.carrier (comparisons (one base))) control
      PV_STX2_SlicePrograms.dispatch
      (PV_STX2_SliceArrayInterpretation.handler (PV_STX2_SliceDriverArrays.handler native)) 107
      ⟨.running (PV_STX2_SliceTypedEntry.entry value),w,[]⟩ =
      ⟨.running (firstClone value),w,[]⟩ := by
  rw [advance_add _ _ _ _ 91 16,initialized_column]
  exact column_cut base control native value w
/-- Conditional on owner acceptance of the translator patch. The f13
activation12 and next counter13 follow from the same original call history. -/
theorem first_activation (value : aspis_statement.state_only_trace.StateOnlyTraceFoundation) :
    (firstClone value).frame.activation = 12 ∧ (firstClone value).store.nextActivation = 13 := ⟨rfl,rfl⟩
/-- Conditional on owner acceptance of the translator patch. The source
clone receives the old column0 reference, while the original wrapper advances
to column1. Neither fact is a supplied OWNER receiver equation. -/
theorem first_operand_and_mutation (value : aspis_statement.state_only_trace.StateOnlyTraceFoundation) :
    (firstClone value).store.cells ⟨12,1,[]⟩ = some (oldReference 0) ∧
    (firstClone value).store.cells ⟨9,2,[]⟩ = some (wrapper 1) := by
  have counter : (PV_STX2_SliceColumnAdvance.stage10 (firstColumn value).store 11 0).nextActivation = 12 := rfl
  simp [firstClone,cloneConfig,cloneStore,PV_STX2_Native.arguments,write,counter,
    borrowed,live,dead,stored]

#print axioms cloneStore
#print axioms cloneConfig
#print axioms source_entry
#print axioms first_captures
#print axioms column_cut
#print axioms firstClone
#print axioms initialized_clone
#print axioms first_activation
#print axioms first_operand_and_mutation
end PV_STX2_SliceCloneEntry
