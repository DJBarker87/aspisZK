import PV_STX2_SliceToVecFinish
set_option autoImplicit false
noncomputable section
namespace PV_STX2_SliceToVecCompletion
open Aeneas Aeneas.Std PV_STX_Machine PV_STX2_Syntax PV_STX2_Store
open PV_STX2_SliceSyntax PV_STX2_SliceMachine PV_STX2_SliceToVecPointers
/-- Conditional on owner acceptance of the translator patch. Exact successful
post-copy store through set_len and lifetime endings, retaining native inner. -/
def finished (s : Store Data) (a : Nat) (inner length : Data) : Store Data :=
  PV_STX2_SliceToVecZero.cleared
    (write (PV_STX2_SliceToVecFinish.checked s a) ⟨a,0,[]⟩
      (some (PV_STX2_SliceToVecFinish.vector inner length))) a
/-- Conditional on owner acceptance of the translator patch. Compose named
post-copy5/set_len1/tail12 without re-proving their instructions. This LOCAL
successful-copy suffix completes f21; it asserts no native copy success,
allocation ownership, original parent reachability, or q association. -/
theorem source18 {W E : Type} (base : Carrier W Data) (control : Control)
    (handler : PV_STX2_Native.Request Data → W → Reply W E Data)
    (s : Store Data) (parent : Frame) (parents : List Frame) (w : W) (a : Nat) (inner length : Data)
    (result : s.cells ⟨a,0,[]⟩ = some (PV_STX2_SliceToVecConstruct.vector inner))
    (len : s.cells ⟨a,3,[]⟩ = some length) :
    advance (carrier base) control PV_STX2_SlicePrograms.dispatch handler 18
      ⟨.running ⟨{activation := a,remaining := PV_STX2_SliceF21.program.body.drop 29},
        parent :: parents,s⟩,w,[]⟩ =
      ⟨.running ⟨{activation := a,remaining := PV_STX2_SliceF21.program.body.drop 46,completed := some (.ok (PV_STX2_SliceToVecFinish.vector inner length))},
        parent :: parents,finished s a inner length⟩,w,[]⟩ := by
  rw [PV_STX2_SliceDriverBuiltin.advance_add _ _ _ _ 5 13,
    PV_STX2_SliceToVecFinish.check5,
    PV_STX2_SliceDriverBuiltin.advance_add _ _ _ _ 1 12]
  rw [PV_STX2_SliceToVecFinish.set1 base control handler
    (PV_STX2_SliceToVecFinish.checked s a) (parent :: parents) w a inner length
    (by simpa [PV_STX2_SliceToVecFinish.checked,write] using result)
    (by simpa [PV_STX2_SliceToVecFinish.checked,write] using len)]
  exact PV_STX2_SliceToVecFinish.tail12 base control handler _ parent parents w a
    (PV_STX2_SliceToVecFinish.vector inner length) (write_same _ _ _)
/-- Conditional on owner acceptance of the translator patch. The same native
inner survives completion inside the returned Vec; source counter and every
other activation remain unchanged by this completed local suffix. -/
theorem cells (s : Store Data) (a : Nat) (inner length : Data) :
    (finished s a inner length).cells ⟨a,0,[]⟩ =
      some (PV_STX2_SliceToVecFinish.vector inner length) ∧
    (finished s a inner length).nextActivation = s.nextActivation ∧
    (∀ q : Address, q.activation ≠ a → (finished s a inner length).cells q = s.cells q) := by
  refine ⟨?_,rfl,?_⟩
  · simp [finished,PV_STX2_SliceToVecZero.cleared,write]
  · intro q other
    have neq : ∀ i, q ≠ (⟨a,i,[]⟩ : Address) := by
      intro i equal
      exact other (congrArg Address.activation equal)
    simp [finished,PV_STX2_SliceToVecZero.cleared,PV_STX2_SliceToVecFinish.checked,write,neq]
/-- Conditional on owner acceptance of the translator patch. Exact zero-length
branch store retains the actual native reply payload through its return. -/
def zeroFinished (s : Store Data) (a : Nat) : Store Data :=
  PV_STX2_SliceToVecZero.cleared
    (write (PV_STX2_SliceToVecBranch.tested s a 0) ⟨a,4,[]⟩ none) a
/-- Conditional on owner acceptance of the translator patch. Compose named
comparison2/branch1/cleanup11/return1 for the actual zero-length body arm.
This LOCAL suffix consumes a constructor result; it never asserts native
allocation success or installs a successful return as an endpoint hypothesis. -/
theorem zero15 {W E : Type} (base : Carrier W Data) (control : Control)
    (handler : PV_STX2_Native.Request Data → W → Reply W E Data)
    (s : Store Data) (parent : Frame) (parents : List Frame) (w : W) (a : Nat) (value : Data)
    (result : s.cells ⟨a,0,[]⟩ = some value)
    (len : s.cells ⟨a,3,[]⟩ = some (.number 0)) :
    advance (PV_STX2_SliceToVecBranch.carrier base) control PV_STX2_SlicePrograms.dispatch handler 15
      ⟨.running ⟨{activation := a,remaining := PV_STX2_SliceF21.program.body.drop 16},
        parent :: parents,s⟩,w,[]⟩ =
      ⟨.running ⟨{activation := a,remaining := PV_STX2_SliceF21.block31.drop 11 ++ PV_STX2_SliceF21.program.body.drop 19,completed := some (.ok value)},
        parent :: parents,zeroFinished s a⟩,w,[]⟩ := by
  rw [PV_STX2_SliceDriverBuiltin.advance_add _ _ _ _ 2 13,
    PV_STX2_SliceToVecBranch.source2 base control handler s (parent :: parents) w a 0 len,
    PV_STX2_SliceDriverBuiltin.advance_add _ _ _ _ 1 12]
  rw [PV_STX2_SliceToVecBranch.branch1 base control handler
    (PV_STX2_SliceToVecBranch.tested s a 0) (parent :: parents) w a false
    (by simp [PV_STX2_SliceToVecBranch.tested,write])]
  simp only [Bool.false_eq_true, ↓reduceIte]
  rw [PV_STX2_SliceDriverBuiltin.advance_add _ _ _ _ 11 1,
    PV_STX2_SliceToVecZero.cleanup11]
  apply PV_STX2_SliceToVecZero.return1
  simpa [PV_STX2_SliceToVecZero.cleared,PV_STX2_SliceToVecBranch.tested,write] using result
#print axioms zeroFinished
#print axioms zero15
#print axioms finished
#print axioms source18
#print axioms cells
end PV_STX2_SliceToVecCompletion
