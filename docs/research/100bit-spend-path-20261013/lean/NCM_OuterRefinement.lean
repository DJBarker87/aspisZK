import NCM_Tree

set_option autoImplicit false
noncomputable section
namespace AspisR1.NCM_OuterRefinement
open Aeneas Aeneas.Std NCE_OpeningCuts
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps

def observe (child : NCM_OuterDirect.Child) : List Nat → Carrier → NCE_FirstFailure.Log × Option Nat × Carrier
  | [],s => ([],none,s)
  | kind::rest,s =>
    let out := child kind s
    if out.2.1 then
      let tail := observe child rest out.2.2
      (out.1++tail.1,tail.2)
    else (out.1,some kind,out.2.2)

/-- Generic composition lemma. The child law is an ordinary proved callee
lemma when used by the top bridge, NEVER a native hypothesis for a whole tree. -/
theorem refinement (H : Bytes → State) (native : NCM_OuterDirect.Child) (slot : NCE_FirstFailure.Slot)
    (batch : Nat) (Good : Carrier → Prop) (kinds : List Nat)
    (law : ∀ kind ∈ kinds, ∀ s, Good s →
      NCM_Tree.Agrees H (native kind s) (slot batch kind s.scratch) s ∧ Good (native kind s).2.2)
    (s : Carrier) (good : Good s) :
    let source := observe native kinds s
    let target := NCE_FirstFailure.observe H slot (kinds.map (fun k => (batch,k))) s.scratch
    source.1 = target.1 ∧ source.2.1 = target.2.1.map Prod.snd ∧ Good source.2.2 ∧
    source.2.2.log = s.log++source.1 ∧
    (source.2.1 = none → source.2.2.scratch = target.2.2) := by
  induction kinds generalizing s with
  | nil => exact ⟨rfl,rfl,good,by simp only [observe,List.append_nil],by intro _;rfl⟩
  | cons kind rest ih =>
    obtain ⟨agreement,nextGood⟩ := law kind (by simp) s good
    cases source : native kind s with
    | mk log actual =>
      rcases actual with ⟨accepted,after⟩
      cases target : eval H (slot batch kind s.scratch) with
      | mk modelLog expected =>
        rcases expected with ⟨modelAccepted,modelAfter⟩
        simp only [NCM_Tree.Agrees,source,target] at agreement
        rw [source] at nextGood
        rcases agreement with ⟨readEq,resultEq,prepared,proof,frame,scratch⟩
        subst modelLog
        subst modelAccepted
        cases accepted with
        | false =>
          simp only [observe,source,List.map_cons,NCE_FirstFailure.observe,target,Bool.false_eq_true,if_false,Option.map_some]
          exact ⟨True.intro,True.intro,nextGood,frame,by intro impossible;cases impossible⟩
        | true =>
          have sameScratch := scratch rfl
          have tail := ih (fun k mem => law k (List.mem_cons_of_mem _ mem)) after nextGood
          rw [sameScratch] at tail
          simp only [observe,source,List.map_cons,NCE_FirstFailure.observe,target,if_true]
          rcases tail with ⟨reads,first,goodAfter,logFrame,final⟩
          refine ⟨congrArg (fun xs => log++xs) reads,first,goodAfter,?_,final⟩
          rw [logFrame,frame,List.append_assoc]

/-- Interpret native phase control on the same direct child observations. -/
theorem control (start : NCE_OuterCuts.Start) (after0 after1 : NCE_OuterCuts.Continue)
    (finish : NCE_OuterCuts.Finish)
    (cut : NCE_OuterCuts.NCE_Native_ThreeTrees start after0 after1 finish)
    (child : NCM_OuterDirect.Child) (s : Carrier) :
    NCM_OuterDirect.execute start after0 after1 finish child s = observe child [0,1,2] s := by
  rw [NCM_OuterDirect.control start after0 after1 finish cut child s]
  simp only [observe]
  cases first : (child 0 s).2.1 <;>
    simp only [first,Bool.false_eq_true,if_true,if_false,List.append_nil,List.append_assoc]
  all_goals
    cases second : (child 1 (child 0 s).2.2).2.1 <;>
      simp only [second,Bool.false_eq_true,if_true,if_false,List.append_nil,List.append_assoc]
  all_goals
    cases third : (child 2 (child 1 (child 0 s).2.2).2.2).2.1 <;>
      simp only [third,Bool.false_eq_true,if_true,if_false,List.append_nil,List.append_assoc]

#print axioms control

#print axioms refinement
end AspisR1.NCM_OuterRefinement
end
