import RPz8_F3U_Pointwise
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3U_Joint
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open AspisV8R19.CausalFirstHitUnionBound

def program {A B C : Type} (p : Program Bytes State A) (q : Program Bytes State B)
    (r : Program Bytes State C) : Program Bytes State (View Bytes State A × View Bytes State B × View Bytes State C) :=
  bind (OracleProgramRecording.record p) fun x=>
  bind (OracleProgramRecording.record q) fun y=>
  bind (OracleProgramRecording.record r) fun z=>.done (x,y,z)

theorem output {A B C : Type} (p : Program Bytes State A) (q : Program Bytes State B)
    (r : Program Bytes State C) (H : Bytes → State) :
    (eval H (program p q r)).2=(eval H p,eval H q,eval H r) := by
  simp only [program,eval_bind,OracleProgramRecording.eval_record,eval]

#print axioms output
end AspisR1.F3U_Joint
end
