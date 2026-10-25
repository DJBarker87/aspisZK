import PAln_Oracle
import SdkC_Oracle
set_option autoImplicit false
noncomputable section
namespace AspisR1.PAln_Log
open Aeneas Aeneas.Std Result
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.SqueezeOracleBridge
open AspisR1PublicPreparation SourceDigestLog
open SdkC_Source

def code : List (Parts × Digest) → Code Unit
  | [] => .done ()
  | call::tail => .read call.1 (fun _ => code tail)

def expected (calls : List (Parts × Digest)) : Log :=
  calls.map (fun call => ⟨call.1,.ok call.2⟩)

theorem run_code (hashv : Parts → Result Digest) (calls : List (Parts × Digest))
    (returns : ∀ c ∈ calls, hashv c.1=.ok c.2) (before : Log) :
    run hashv (code calls) before=(.ok (),before++expected calls) := by
  induction calls generalizing before with
  | nil => simp only [code,run,expected,List.map_nil,List.append_nil]
  | cons call tail ih =>
    have first := returns call (List.mem_cons_self)
    simp only [code,run,first]
    rw [ih (fun c member => returns c (List.mem_cons_of_mem _ member))]
    simp only [expected,List.map_cons,List.append_assoc,List.singleton_append]

def callParts {D : aspis_core.Digest32 Unit} {pre : r1_wire.Prefix}
    (c : SourceFull25.Call D pre) : List (Parts × Digest) :=
  [(TranscriptStep.absorbParts c.before.state c.tag c.record.framed,c.absorbed),
   (TranscriptStep.readParts c.absorbed 1#u8,c.block),
   (TranscriptStep.readParts c.absorbed 2#u8,c.state)]

def sourceParts {D : aspis_core.Digest32 Unit} {pre : r1_wire.Prefix}
    (cs : List (SourceFull25.Call D pre)) : List (Parts × Digest) := cs.flatMap callParts

theorem source_returns (D : aspis_core.Digest32 Unit) (hashv : Parts → Result Digest)
    (binding : ∀ self parts,D.digest self parts=hashv parts)
    (pre : r1_wire.Prefix) (cs : List (SourceFull25.Call D pre)) :
    ∀ q ∈ sourceParts cs,hashv q.1=.ok q.2 := by
  intro q member
  obtain ⟨c,member,entry⟩ := List.mem_flatMap.mp member
  simp only [callParts,List.mem_cons,List.not_mem_nil,or_false] at entry
  rcases entry with rfl | rfl | rfl
  · rw [← binding c.before.hash]; exact c.absorb
  · rw [← binding c.before.hash]; exact c.read1
  · rw [← binding c.before.hash]; exact c.read2

theorem read_expected {D : aspis_core.Digest32 Unit} {pre : r1_wire.Prefix}
    (cs : List (SourceFull25.Call D pre)) :
    readLog (expected (sourceParts cs))=sourceLog cs := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
    simp only [sourceParts,List.flatMap_cons,expected,List.map_append,SdkC_Oracle.readLog_append]
    change callLog c ++ readLog (expected (sourceParts cs))=callLog c++sourceLog cs
    rw [ih]

theorem source_replay (D : aspis_core.Digest32 Unit) (hashv : Parts → Result Digest)
    (binding : ∀ self parts,D.digest self parts=hashv parts)
    (pre : r1_wire.Prefix) (cs : List (SourceFull25.Call D pre)) :
    (run hashv (code (sourceParts cs)) []).1=.ok () ∧
    readLog (run hashv (code (sourceParts cs)) []).2=sourceLog cs := by
  rw [run_code hashv _ (source_returns D hashv binding pre cs)]
  exact ⟨rfl,read_expected cs⟩

#print axioms run_code
#print axioms source_returns
#print axioms read_expected
#print axioms source_replay
end AspisR1.PAln_Log
end
