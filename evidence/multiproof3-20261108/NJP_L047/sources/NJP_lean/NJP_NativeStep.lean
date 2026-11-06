import NJP_NativeRowCut

set_option autoImplicit false
noncomputable section
namespace NJP_NativeStep
open Aeneas Aeneas.Std Result NJP_RowModel NJP_NativeRowCut
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps

/-- The exact native caller postconditions, with the CLOSED digest child
installed at the SAME logged arguments, give the complete source-G step.
All fields, including failed/empty prefixes and untouched buffer coordinates,
are retained. No whole-loop or successful-child equality is a hypothesis. -/
theorem one (H : Request → Digest) (nodes : Nat → U8) (length : Nat)
    (s : Scratch) (i w : Nat) (after : Scratch) (ni nw : Nat)
    (returned : Bool) (log : Log)
    (cut : Cut s i w length nodes (H (request log)) after ni nw returned log) :
 eval H (node nodes length s i w)=
 (if log.calls=0 then [] else [(request log,H (request log))],
  ok (if returned then Row.next after ni nw else Row.stop after)) := by
 have post := state s i w length nodes (H (request log)) after ni nw returned log cut
 by_cases active : i<s.n
 · by_cases both : paired s i
   · have entered : writes s i length := ⟨active,Or.inl both⟩
     have args := arguments s i w length nodes (H (request log)) after ni nw returned log cut entered
     simp only [if_pos both] at args
     rw [occupied_observation H nodes length s i w active both]
     simp only [cut.count,if_pos entered,show ¬(1:Nat)=0 by decide,if_false,args,
       cut.returnValue,active,not_true,both,false_or,true_or,decide_true,ite_true,
       post,if_pos entered,cut.nextIndex,nextI,if_pos active,if_pos both,
       cut.nextWrite,if_pos entered,cursor,active,both,not_true,and_false,false_and,true_and,and_true,if_false]
   · by_cases available : s.cursor+32 ≤ length
     · have entered : writes s i length := ⟨active,Or.inr available⟩
       have args := arguments s i w length nodes (H (request log)) after ni nw returned log cut entered
       simp only [if_neg both] at args
       rw [sibling_observation H nodes length s i w active both available]
       simp only [cut.count,if_pos entered,show ¬(1:Nat)=0 by decide,if_false,args,
         cut.returnValue,active,not_true,both,false_or,available,or_true,decide_true,ite_true,
         post,if_pos entered,cut.nextIndex,nextI,if_pos active,if_neg both,if_pos available,
         cut.nextWrite,if_pos entered,cursor,active,both,not_false,and_self,false_and,true_and,and_true,if_true]
     · have absent : ¬writes s i length := by intro h;exact available (h.2.resolve_left both)
       rw [missing_observation H nodes length s i w active both (by omega)]
       simp only [cut.count,if_neg absent,ite_true,cut.returnValue,active,not_true,both,
         available,false_or,decide_false,Bool.false_eq_true,ite_false,post,if_neg absent]
 · have absent : ¬writes s i length := fun h => active h.1
   rw [exhausted_observation H nodes length s i w (by omega)]
   simp only [cut.count,if_neg absent,ite_true,cut.returnValue,active,not_false,true_or,
     decide_true,ite_true,post,if_neg absent,cut.nextIndex,nextI,if_neg active,cut.nextWrite,if_neg absent]

#print one
#print axioms one
end NJP_NativeStep
end
