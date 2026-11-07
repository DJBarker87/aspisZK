import PV_FN_SLICE_f7_Prefix
import PV_FN_W2_BinaryEnter
set_option autoImplicit false
noncomputable section
namespace PV_FN_SLICE_f7_Into8
open Aeneas Aeneas.Std PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine PV_EVHB_OwnerMachine
open PV_FN_SLICE_f7_Prefix

theorem enter8 {E : Type} (x : Input E)
    (resolve8 : x.P source.2.1 = some PV_STX2_SliceF8.program) :
    PV_THR2_IntrinsicState.advance (PV_FN_SLICE_ValueCarrier.carrier x.C) x.K x.P x.H 1 (out x) =
      ⟨⟨.running ⟨{activation := (input8 x).a,remaining := PV_STX2_SliceF8.program.body},
        (input8 x).parent :: (input8 x).parents,(input8 x).s⟩,(input8 x).w,(input8 x).es⟩,(input8 x).stack⟩ := by
  exact PV_FN_W2_BinaryEnter.enter (PV_FN_SLICE_ValueCarrier.carrier x.C) x.K x.P x.H
    (issued x) x.a x.s.nextActivation (PV_STX2_SliceF7.program.body.drop 4) []
    (x.parent :: x.parents) (waiting x) source.2.1 (self x) (tuple x)
    PV_STX2_SliceF8.program x.w x.es x.stack rfl resolve8

/-- First actual consumer of f8's stated conditional provider theorem. Its
representation and pending dependency are imported BY NAME. This is the f7
prefix and callee8 stage; source drop178 and final f7 return remain outside it. -/
theorem through8 {E : Type} (x : Input E) (pre : Pre x)
    (resolve8 : x.P source.2.1 = some PV_STX2_SliceF8.program)
    (resolve6 : x.P PV_FN_SLICE_f8_PrefixData.source.2.1 = some PV_STX2_SliceF6.program)
    (callee6 : PV_FN_SLICE_f6Consumer.Contract (input8 x)) :
    PV_FN_SLICE_f8.Post (input8 x) ∧
    ∃ o : PV_FN_SLICE_f8_FullReplies.Outcome E,
      PV_FN_SLICE_f8_FullReplies.Executed6 (input8 x) o ∧
      ∃ n, PV_THR2_IntrinsicState.advance (PV_FN_SLICE_ValueCarrier.carrier x.C) x.K x.P x.H n
        ⟨⟨.running ⟨{activation := x.a,remaining := PV_STX2_SliceF7.program.body},
          x.parent :: x.parents,x.s⟩,x.w,x.es⟩,x.stack⟩ =
        PV_FN_SLICE_f8_FullReplies.finish (input8 x) o := by
  have closed8 := PV_FN_SLICE_f8.contract (input8 x) (pre8 x pre resolve6) callee6
  refine ⟨closed8,?_⟩
  obtain ⟨o,executed,pending,first,⟨n,body⟩,rest⟩ := closed8
  refine ⟨o,executed,4+1+n,?_⟩
  rw [PV_THR2_IntrinsicComposition.advance_add,PV_THR2_IntrinsicComposition.advance_add,
    PV_FN_SLICE_f7_Prefix.run x pre,enter8 x resolve8]
  exact body

/-- Prefix frame: the borrowed capture stays at the actual f7 LOCAL1; only
f7's scratch slots and the source-minted f8 argument slots are written. -/
theorem frame {E : Type} (x : Input E) (p : Address)
    (own : p.activation ≠ x.a) (child : p.activation ≠ x.s.nextActivation) :
    (issued x).cells p = x.s.cells p := by
  have diff (n : Nat) : p ≠ (⟨x.a,n,[]⟩ : Address) := by
    intro h; exact own (congrArg Address.activation h)
  have freshDiff (n : Nat) : p ≠ (⟨x.s.nextActivation,n,[]⟩ : Address) := by
    intro h; exact child (congrArg Address.activation h)
  simp only [issued,PV_THR2_StaticCall.issued,PV_STX2_Native.arguments,moved,
    store3,store2,store1,write,if_neg (diff 0),if_neg (diff 2),if_neg (diff 3),
    if_neg (freshDiff 1),if_neg (freshDiff 2)]
#print axioms enter8
#print axioms through8
#print axioms frame
set_option pp.fullNames true in
set_option pp.piBinderNames true in
set_option pp.proofs false in
#print through8
end PV_FN_SLICE_f7_Into8
