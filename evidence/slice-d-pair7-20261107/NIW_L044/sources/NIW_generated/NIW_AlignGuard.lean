import NIW_AlignControl
set_option autoImplicit false
noncomputable section
namespace AspisR1.NIW_AlignGuard
open Aeneas Aeneas.Std Result NIT_Cuts NIW_AlignBoundary NIW_AlignControl Classical

/-- Source continuation tag 4 extends the supplied entered-call prefix only
when that prefix returns Ok. All callee replies are the supplied native ones. -/
def project (shared : Bool) (l : Log) (out : Reply Unit) : SameGuard :=
 {skeleton shared l with
  count:=l.count + if out=.Ok () then 1 else 0
  events:=fun i=>if i=l.count ∧ out=.Ok () then 4 else l.events i}

theorem from_cut (shared : Bool) (address : Nat) (i slot power : Nat) (l : Log)
 (afterScratch : NIT_PairControl.Scratch) (afterParts : Parts) (out : Reply Unit)
 (native : cut shared address i slot power l afterScratch afterParts out) :
 cutSameGuard shared (project shared l out) out := by
 rcases native with ⟨_,_,_,_,_,_,reply,count,e0,partialEvents,highEvent,_⟩
 have baseCount : l.count=countBase shared l := count
 have positive : 1≤l.count := by
  rw [baseCount]
  unfold countBase
  split
  · omega
  · split <;> omega
 have partialBound : enteredPartial shared l → 3≤l.count := by
  intro entered
  rw [baseCount]
  unfold countBase
  simp only [if_neg (not_not_intro entered)]
  split <;> omega
 have highBound : enteredHigh shared l → 4≤l.count := by
  intro entered
  rw [baseCount]
  simp [countBase,entered.1,entered]
 refine ⟨rfl,?_,?_,?_,?_,?_⟩
 · exact reply.trans (expected_reply shared l).symm
 · change l.count + (if out=.Ok () then 1 else 0)=(sameExpected shared (skeleton shared l)).2
   rw [expected_count,←baseCount,←reply]
 · have different : (0:Nat)≠l.count := by omega
   simp [project,skeleton,different,e0]
 · intro sameShared regularOk
   have entered : enteredPartial shared l := ⟨regularOk,sameShared⟩
   have bound := partialBound entered
   obtain ⟨event1,event2⟩ := partialEvents entered
   have different1 : (1:Nat)≠l.count := by omega
   have different2 : (2:Nat)≠l.count := by omega
   refine ⟨?_,?_,?_⟩
   · simp [project,skeleton,different1,event1]
   · simp [project,skeleton,different2,event2]
   · intro partialOk
     have values : ∃ values,l.partialReply=.Ok values := by
      cases observed : l.partialReply with
      | Err error=>simp [project,skeleton,erasePartial,observed] at partialOk
      | Ok values=>exact ⟨values,rfl⟩
     have reached : enteredHigh shared l := ⟨entered,values⟩
     have bound := highBound reached
     have different3 : (3:Nat)≠l.count := by omega
     have event3 := highEvent reached
     simp [project,skeleton,different3,event3]
 · intro returned
   have countEnd : (project shared l out).count-1=l.count := by simp [project,returned]
   rw [countEnd]
   simp [project,returned]

#print axioms from_cut
end AspisR1.NIW_AlignGuard
