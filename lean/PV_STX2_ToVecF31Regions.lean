import PV_STX2_ToVecReturnRegion
import PV_STX2_Source7QUniform2Return_layout7
import PV_STX2_Source7QUniform2Return_capacity4
import PV_STX2_Source7QUniform2Return_assert9
set_option autoImplicit false
noncomputable section
namespace PV_STX2_ToVecF31Regions
open Aeneas Aeneas.Std PV_STX_Machine PV_STX2_Syntax PV_STX2_Store
open PV_STX2_SliceMachine PV_EVHB_OWNER
/-- Conditional on owner acceptance of the translator patch. Reuse the
six generated Layout operands and their key selection, with arbitrary f31
activation and saved callers, consuming the existing source7 law BY NAME. -/
theorem source7 (resources : Resources) (encode : Encode)
    (base : Carrier PV_STX_World.World Data) (K : Control)
    (P : Data → Option PV_STX2_SliceSyntax.Program)
    (H : PV_STX2_Native.Request Data → OWNER → Reply OWNER PV_RJ4IDB.NativeEvent Data)
    (s : Store Data) (parents : List Frame) (a : Nat) (w : OWNER)
    (prior : List PV_RJ4IDB.NativeEvent)
    (input : s.cells ⟨a,3,[]⟩ = some PV_STX2_Source7LayoutConstructor.value) :
    PV_STX2_Source7IterationBindings.advance resources encode
      (PV_STX2_Source7QUniformReturnCompatibility.C base K H) K P H 7
      ⟨.running ⟨{activation := a,remaining := PV_STX2_Source7CtorF31.program.body.drop 9},parents,s⟩,w,prior⟩ =
      ⟨.running ⟨{activation := a,remaining := PV_STX2_Source7CtorF31.block35 ++
        PV_STX2_Source7CtorF31.program.body.drop 16},parents,PV_STX2_Source7QF31Layout.stored s a⟩,w,prior⟩ := by
  let C := PV_STX2_Source7QUniformReturnCompatibility.C base K H
  apply PV_STX2_ToVecReturnRegion.last resources encode base K P H
    PV_STX2_Source7QUniform2Return_layout7.nodes
    (PV_STX2_Source7CtorF31.node36 :: PV_STX2_Source7CtorF31.program.body.drop 16) a parents s w prior
  · intro node hn
    simp only [PV_STX2_Source7QUniform2Return_layout7.nodes,List.mem_cons,List.not_mem_nil,or_false] at hn
    rcases hn with rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first
      | exact Or.inl True.intro
      | exact Or.inr ⟨_,rfl,True.intro,by first | exact True.intro | constructor <;> trivial⟩
  · intro node hn
    simp only [PV_STX2_Source7QUniform2Return_layout7.nodes,List.mem_cons,List.not_mem_nil,or_false] at hn
    rcases hn with rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first | rfl | trivial
  · intro stored; exact ⟨True.intro,rfl⟩
  · exact PV_STX2_Source7QF31Layout.source7 (PV_STX2_Source7QF31Assert.scalars C) K H s parents a w input
/-- Conditional on owner acceptance of the translator patch. Reuse the
four generated capacity-read instructions and the existing source4 law. -/
theorem source4 (resources : Resources) (encode : Encode)
    (base : Carrier PV_STX_World.World Data) (K : Control)
    (P : Data → Option PV_STX2_SliceSyntax.Program)
    (H : PV_STX2_Native.Request Data → OWNER → Reply OWNER PV_RJ4IDB.NativeEvent Data)
    (s : Store Data) (parents : List Frame) (after : List PV_STX2_SliceSyntax.Node)
    (a cap : Nat) (ptr alloc : Data) (w : OWNER) (prior : List PV_RJ4IDB.NativeEvent)
    (input : s.cells ⟨a,0,[]⟩ = some (PV_STX2_Aggregates.pack
      PV_STX2_Source7QHeaderStep.kind [ptr,.number cap,alloc])) :
    PV_STX2_Source7IterationBindings.advance resources encode
      (PV_STX2_Source7QUniformReturnCompatibility.C base K H) K P H 4
      ⟨.running ⟨{activation := a,remaining := PV_STX2_Source7CtorF31.block35 ++ after},parents,s⟩,w,prior⟩ =
      ⟨.running ⟨{activation := a,remaining := after},parents,PV_STX2_Source7QF31Capacity.stored s a cap⟩,w,prior⟩ := by
  let C := PV_STX2_Source7QUniformReturnCompatibility.C base K H
  apply PV_STX2_ToVecReturnRegion.straight resources encode base K P H
    PV_STX2_Source7QUniform2Return_capacity4.nodes after a parents s w prior
  · intro node hn
    simp only [PV_STX2_Source7QUniform2Return_capacity4.nodes,List.mem_cons,List.not_mem_nil,or_false] at hn
    rcases hn with rfl | rfl | rfl | rfl
    all_goals first
      | exact Or.inl True.intro
      | exact Or.inr ⟨_,rfl,True.intro,by first | exact True.intro | constructor <;> trivial⟩
  · intro node hn
    simp only [PV_STX2_Source7QUniform2Return_capacity4.nodes,List.mem_cons,List.not_mem_nil,or_false] at hn
    rcases hn with rfl | rfl | rfl | rfl
    all_goals first | rfl | trivial
  · exact PV_STX2_Source7QF31Capacity.source4
      (PV_STX2_Source7AllocationRuntimeBranch.keys (PV_STX2_Source7QF31Assert.scalars C)) K H
      s parents after a cap ptr alloc w input
/-- Conditional on owner acceptance of the translator patch. Reuse the
nine generated assertion operands and wrapping-subtraction control law. -/
theorem source9 (resources : Resources) (encode : Encode)
    (base : Carrier PV_STX_World.World Data) (ctrl : Control)
    (P : Data → Option PV_STX2_SliceSyntax.Program)
    (H : PV_STX2_Native.Request Data → OWNER → Reply OWNER PV_RJ4IDB.NativeEvent Data)
    (s : Store Data) (parents : List Frame) (a cap : Nat) (w : OWNER)
    (prior : List PV_RJ4IDB.NativeEvent)
    (bounded : cap < PV_STX2_Source7CapacityScalars.modulus)
    (capacity : s.cells ⟨a,10,[]⟩ = some (.number cap))
    (requested : s.cells ⟨a,1,[]⟩ = some (.number cap)) :
    let K := PV_STX2_Source7QF31Assert.control ctrl
    PV_STX2_Source7IterationBindings.advance resources encode
      (PV_STX2_Source7QUniformReturnCompatibility.C base K H) K P H 9
      ⟨.running ⟨{activation := a,remaining := PV_STX2_Source7CtorF31.program.body.drop 16},parents,s⟩,w,prior⟩ =
      ⟨.running ⟨{activation := a,remaining := PV_STX2_Source7CtorF31.program.body.drop 25},parents,
        PV_STX2_Source7QF31Assert.stored s a cap⟩,w,prior⟩ := by
  dsimp only
  let K := PV_STX2_Source7QF31Assert.control ctrl
  let C := PV_STX2_Source7QUniformReturnCompatibility.C base K H
  apply PV_STX2_ToVecReturnRegion.straight resources encode base K P H
    PV_STX2_Source7QUniform2Return_assert9.nodes (PV_STX2_Source7CtorF31.program.body.drop 25) a parents s w prior
  · intro node hn
    simp only [PV_STX2_Source7QUniform2Return_assert9.nodes,List.mem_cons,List.not_mem_nil,or_false] at hn
    rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first
      | exact Or.inl True.intro
      | exact Or.inr ⟨_,rfl,True.intro,by first | exact True.intro | constructor <;> trivial⟩
  · intro node hn
    simp only [PV_STX2_Source7QUniform2Return_assert9.nodes,List.mem_cons,List.not_mem_nil,or_false] at hn
    rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first | rfl | trivial
  · exact PV_STX2_Source7QF31Assert.source9 (PV_STX2_Source7AllocationRuntimeBranch.keys C)
      ctrl H s parents a cap w bounded capacity requested
#print axioms source7
#print axioms source4
#print axioms source9
end PV_STX2_ToVecF31Regions
