import PV_STX2_ToVecReturnRegion
import PV_STX2_CallSummarySelectedGuard
import PV_STX2_Source7QUniform2Return_cleanup12
set_option autoImplicit false
noncomputable section
namespace PV_STX2_ToVecF31Return
open Aeneas Aeneas.Std PV_STX_Machine PV_STX2_Syntax PV_STX2_Store
open PV_STX2_SliceMachine PV_EVHB_OWNER
/-- Conditional on owner acceptance of the translator patch. Reuse the
named f31 return law, its selected pinned guard and generated cleanup syntax
at any activation, preserving every computed store and saved caller. -/
theorem source13 (resources : Resources) (encode : Encode)
    (base : Carrier PV_STX_World.World Data) (K : Control)
    (P : Data → Option PV_STX2_SliceSyntax.Program)
    (H : PV_STX2_Native.Request Data → OWNER → Reply OWNER PV_RJ4IDB.NativeEvent Data)
    (s : Store Data) (parent : Frame) (parents : List Frame) (a : Nat)
    (inner : Data) (w : OWNER) (prior : List PV_RJ4IDB.NativeEvent)
    (input : s.cells ⟨a,0,[]⟩ = some inner)
    (guard : s.cells ⟨a,14,[]⟩ = some (.boolean false))
    (assertion : s.cells ⟨a,5,[]⟩ = some (.boolean true)) :
    PV_STX2_Source7IterationBindings.advance resources encode
      (PV_STX2_Source7QUniformReturnCompatibility.C base K H) K P H 13
      ⟨.running ⟨{activation := a,remaining := PV_STX2_Source7CtorF31.program.body.drop 25},parent::parents,s⟩,w,prior⟩ =
      ⟨.running ⟨{activation := a,remaining := [PV_STX2_Source7CtorF31.node63],completed := some (.ok inner)},
        parent::parents,PV_STX2_Source7QF31Return.stored s a⟩,w,prior⟩ := by
  let C := PV_STX2_Source7QUniformReturnCompatibility.C base K H
  let D := PV_STX2_Source7QUniformReturnCompatibility.localCarrier C
  let rest := PV_STX2_Source7CtorF31.program.body.drop 26
  let cut := write s ⟨a,14,[]⟩ none
  have operandD : operand D s w a (.move (.local 14)) = some (.boolean false,cut) := by
    simp [operand,PV_STX2_Store.read,locate,writeAddress,guard,cut]
  have truthD : D.truth (.boolean false) = some false := rfl
  have first : advance D K (fun _ => none) H 1
      ⟨.running ⟨{activation := a,remaining := PV_STX2_Source7CtorF31.program.body.drop 25},parent::parents,s⟩,w,[]⟩ =
      ⟨.running ⟨{activation := a,remaining := rest},parent::parents,cut⟩,w,[]⟩ := by
    change advance D K (fun _ => none) H 1
      ⟨.running ⟨{activation := a,remaining := PV_STX2_Source7CtorF31.node49 :: rest},parent::parents,s⟩,w,[]⟩ = _
    simp only [PV_STX2_SliceMachine.advance,PV_STX2_SliceMachine.step,
      PV_STX2_Source7CtorF31.node49,operandD,truthD,PV_STX2_Source7CtorF31.block48,
      List.nil_append,List.append_nil]
    rfl
  have old := PV_STX2_Source7QF31Return.source13
    (PV_STX2_Source7AllocationRuntimeBranch.keys (PV_STX2_Source7QF31Assert.scalars C))
    K H s parent parents a w inner input guard assertion
  change advance D K (fun _ => none) H 13 _ = _ at old
  rw [show 13=1+12 by omega,PV_STX2_SliceDriverBuiltin.advance_add,first] at old
  have tail := PV_STX2_ToVecReturnRegion.last resources encode base K P H
    PV_STX2_Source7QUniform2Return_cleanup12.nodes [PV_STX2_Source7CtorF31.node63]
    a (parent::parents) cut w prior
    ⟨{activation := a,remaining := [PV_STX2_Source7CtorF31.node63],completed := some (.ok inner)},
      parent::parents,PV_STX2_Source7QF31Return.stored s a⟩
    (by intro node hn
        simp only [PV_STX2_Source7QUniform2Return_cleanup12.nodes,List.mem_cons,List.not_mem_nil,or_false] at hn
        rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
        all_goals first
          | exact Or.inl True.intro
          | exact Or.inr ⟨_,rfl,True.intro,True.intro⟩)
    (by intro node hn
        simp only [PV_STX2_Source7QUniform2Return_cleanup12.nodes,List.mem_cons,List.not_mem_nil,or_false] at hn
        rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
        all_goals first | rfl | trivial)
    (by intro stored; exact ⟨True.intro,rfl⟩) old
  have installedFirst := PV_STX2_CallSummarySelectedGuard.selected resources encode C K P H a
    ⟨31,780,.array [.atom "body",.atom "statements",.number 25]⟩ (.move (.local 14))
    PV_STX2_Source7CtorF31.block47 PV_STX2_Source7CtorF31.block48 rest (parent::parents)
    s cut w prior (.boolean false) false
    (by simp [operand,PV_STX2_Store.read,locate,writeAddress,guard,cut]) rfl
  change PV_STX2_Source7IterationBindings.advance resources encode C K P H 1
    ⟨.running ⟨{activation := a,remaining := PV_STX2_Source7CtorF31.program.body.drop 25},parent::parents,s⟩,w,prior⟩ =
    ⟨.running ⟨{activation := a,remaining := rest},parent::parents,cut⟩,w,prior⟩ at installedFirst
  rw [show 13=1+12 by omega,PV_STX2_Source7IterationBindings.advance_add,installedFirst]
  exact tail
#print axioms source13
end PV_STX2_ToVecF31Return
