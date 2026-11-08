import PV_STX2_SliceToVecCopy
set_option autoImplicit false
noncomputable section
namespace PV_STX2_SliceToVecFinish
open Aeneas Aeneas.Std PV_STX_Machine PV_STX2_Syntax PV_STX2_Store
open PV_STX2_SliceSyntax PV_STX2_SliceMachine PV_STX2_SliceToVecPointers
/-- Conditional on owner acceptance of the translator patch. Source Vec after
set_len retains the SAME native inner reply and changes only its length field. -/
def vector (inner length : Data) : Data :=
  PV_STX2_Aggregates.pack (PV_STX2_SliceClosureStores.kind PV_STX2_SliceF21.node14)
    [PV_STX2_SliceToVecConstruct.raw inner,length]
/-- Conditional on owner acceptance of the translator patch. Exact source
Vec length-field replacement preserves RawVec and its native descriptor. -/
theorem replace_length {W : Type} (base : Carrier W Data) (inner length : Data) :
    (carrier base).replaceField (PV_STX2_SliceToVecConstruct.vector inner) 1
      (some length) = some (vector inner length) := rfl
/-- Conditional on owner acceptance of the translator patch. Five actual
post-copy instructions end pointer lifetimes and select the pinned false
set_len UB-check branch. Its checking syntax remains in the source program. -/
def checked (s : Store Data) (a : Nat) : Store Data :=
  write (write (write (write (write s ⟨a,6,[]⟩ none) ⟨a,5,[]⟩ none)
    ⟨a,18,[]⟩ none) ⟨a,18,[]⟩ (some (.boolean false))) ⟨a,18,[]⟩ none
/-- Conditional on owner acceptance of the translator patch. Actual post-copy
source branch, with all store/world/parents retained. -/
theorem check5 {W E : Type} (base : Carrier W Data) (control : Control)
    (handler : PV_STX2_Native.Request Data → W → Reply W E Data)
    (s : Store Data) (parents : List Frame) (w : W) (a : Nat) :
    advance (carrier base) control PV_STX2_SlicePrograms.dispatch handler 5
      ⟨.running ⟨{activation := a,remaining := PV_STX2_SliceF21.program.body.drop 29},parents,s⟩,w,[]⟩ =
      ⟨.running ⟨{activation := a,remaining := PV_STX2_SliceF21.program.body.drop 34},
        parents,checked s a⟩,w,[]⟩ := by
  have ub : (carrier base).nullary w (.array [.atom "UbChecks",
      .object [("Deduplicated",.number 1715)]]) = some (.boolean false) := rfl
  have truth : (carrier base).truth (.boolean false) = some false := rfl
  simp [PV_STX2_SliceMachine.advance,PV_STX2_SliceMachine.step,
    PV_STX2_SliceF21.program,PV_STX2_SliceF21.block83,
    PV_STX2_SliceF21.node52,PV_STX2_SliceF21.node53,PV_STX2_SliceF21.node54,
    PV_STX2_SliceF21.node55,PV_STX2_SliceF21.node69,PV_STX2_SliceF21.block68,
    native,adopt,PV_STX2_Native.step,PV_STX2_Store.bind,evaluate,operand,
    PV_STX2_Store.read,locate,writeAddress,write,ub,truth,checked]
/-- Conditional on owner acceptance of the translator patch. Actual set_len
writes the copied metadata length into LOCAL0's source Vec field1. No native
capacity, byte-copy validity or ownership is inferred from this local law. -/
theorem set1 {W E : Type} (base : Carrier W Data) (control : Control)
    (handler : PV_STX2_Native.Request Data → W → Reply W E Data)
    (s : Store Data) (parents : List Frame) (w : W) (a : Nat) (inner length : Data)
    (result : s.cells ⟨a,0,[]⟩ = some (PV_STX2_SliceToVecConstruct.vector inner))
    (len : s.cells ⟨a,3,[]⟩ = some length) :
    advance (carrier base) control PV_STX2_SlicePrograms.dispatch handler 1
      ⟨.running ⟨{activation := a,remaining := PV_STX2_SliceF21.program.body.drop 34},parents,s⟩,w,[]⟩ =
      ⟨.running ⟨{activation := a,remaining := PV_STX2_SliceF21.program.body.drop 35},
        parents,write s ⟨a,0,[]⟩ (some (vector inner length))⟩,w,[]⟩ := by
  simp [PV_STX2_SliceMachine.advance,PV_STX2_SliceMachine.step,
    PV_STX2_SliceF21.program,PV_STX2_SliceF21.block83,PV_STX2_SliceF21.node70,
    native,adopt,PV_STX2_Native.step,PV_STX2_Store.bind,evaluate,operand,
    PV_STX2_Store.read,locate,writeAddress,replaceFields,result,len,replace_length]
/-- Conditional on owner acceptance of the translator patch. Eleven actual
lifetime endings and the final source return preserve the SAME Vec payload
and complete f21 under its original saved parent stack. -/
theorem tail12 {W E : Type} (base : Carrier W Data) (control : Control)
    (handler : PV_STX2_Native.Request Data → W → Reply W E Data)
    (s : Store Data) (parent : Frame) (parents : List Frame) (w : W) (a : Nat) (value : Data)
    (result : s.cells ⟨a,0,[]⟩ = some value) :
    advance (carrier base) control PV_STX2_SlicePrograms.dispatch handler 12
      ⟨.running ⟨{activation := a,remaining := PV_STX2_SliceF21.program.body.drop 35},parent :: parents,s⟩,w,[]⟩ =
      ⟨.running ⟨{activation := a,remaining := PV_STX2_SliceF21.program.body.drop 46,completed := some (.ok value)},parent :: parents,PV_STX2_SliceToVecZero.cleared s a⟩,w,[]⟩ := by
  simp [PV_STX2_SliceMachine.advance,PV_STX2_SliceMachine.step,
    PV_STX2_SliceF21.program,PV_STX2_SliceF21.block83,
    PV_STX2_SliceF21.node71,PV_STX2_SliceF21.node72,PV_STX2_SliceF21.node73,
    PV_STX2_SliceF21.node74,PV_STX2_SliceF21.node75,PV_STX2_SliceF21.node76,
    PV_STX2_SliceF21.node77,PV_STX2_SliceF21.node78,PV_STX2_SliceF21.node79,
    PV_STX2_SliceF21.node80,PV_STX2_SliceF21.node81,PV_STX2_SliceF21.node82,
    native,adopt,PV_STX2_Native.step,PV_STX2_Store.read,result,
    PV_STX2_SliceToVecZero.cleared,write]
#print axioms vector
#print axioms replace_length
#print axioms checked
#print axioms check5
#print axioms set1
#print axioms tail12
end PV_STX2_SliceToVecFinish
