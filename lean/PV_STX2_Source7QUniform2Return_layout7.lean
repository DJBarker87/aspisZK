import PV_STX2_Source7QUniformStraightTrace2
import PV_STX2_Source7CtorF31
set_option autoImplicit false
noncomputable section
namespace PV_STX2_Source7QUniform2Return_layout7
open Aeneas Aeneas.Std PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_EVHB_OWNER
open PV_STX2_SliceMachine PV_STX2_Source7QUniformTrace2
/-- Conditional on owner acceptance of the translator patch. Existing return
region layout7, excluding the enlarged sites by instruction shape. -/
def nodes : List PV_STX2_SliceSyntax.Node := [PV_STX2_Source7CtorF31.node23, PV_STX2_Source7CtorF31.node24, PV_STX2_Source7CtorF31.node25, PV_STX2_Source7CtorF31.node26, PV_STX2_Source7CtorF31.node27, PV_STX2_Source7CtorF31.node28]
/-- Conditional on owner acceptance of the translator patch. Whole-segment
certificate with the actual loop stack and every bind outcome retained. -/
theorem run {E : Type} (C : Carrier OWNER Data) (K : Control)
    (P : Data → Option PV_STX2_SliceSyntax.Program)
    (H : PV_STX2_Native.Request Data → OWNER → Reply OWNER E Data)
    (n a : Nat) (rest : List PV_STX2_SliceSyntax.Node) (parents : List Frame)
    (loops : List LoopFrame) (store : Store Data) (w : OWNER) (events : List E)
    (tail : ∀ stored world es, Trace C K P H n
      ⟨.running ⟨{activation := a,remaining := rest,loops := loops},parents,stored⟩,world,es⟩) :
    Trace C K P H (6+n)
      ⟨.running ⟨{activation := a,remaining := nodes ++ rest,loops := loops},parents,store⟩,w,events⟩ := by
  change Trace C K P H (nodes.length+n) _
  apply PV_STX2_Source7QUniformStraightTrace2.then_run
  · intro node hn
    simp only [nodes,List.mem_cons,List.not_mem_nil,or_false] at hn
    rcases hn with rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first
      | exact Or.inl True.intro
      | exact Or.inr ⟨_,rfl,True.intro,by first | exact True.intro | constructor <;> trivial⟩
  · intro node hn
    simp only [nodes,List.mem_cons,List.not_mem_nil,or_false] at hn
    rcases hn with rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first | rfl | trivial
  · exact tail
#print axioms nodes
#print axioms run
end PV_STX2_Source7QUniform2Return_layout7
