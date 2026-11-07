import NND_Stage1Eval
set_option autoImplicit false
namespace NND_Stage1RefEval
open RSL RSL.TX1_345 NND_Returned

def value (V : VLib) (P : PreparedNew V) (F : NND_Tx1ReturnedValues.Values V P)
 (C : S1Lib V) (a : Args) (env : Env) : Except ProgramError Bytes :=
 if badRoute a then .error .invalidInstructionData else
 match a.accounts with
 | [p,pub,ck] => NND_Stage1Eval.bodyValue V P F C a p pub ck env
 | _ => .ok []

theorem returned (V : VLib) (P : PreparedNew V) (F : NND_Tx1ReturnedValues.Values V P)
 (C : S1Lib V) (a : Args) (env : Env) :
 Returns (Ref V P C a) env (value V P F C a env) := by
 unfold Ref value
 split
 · exact throw env _
 · cases ha : a.accounts with
   | nil => exact rs_lift _ env [] (panic env [])
   | cons p xs =>
     cases xs with
     | nil => exact rs_lift _ env [] (panic env [])
     | cons pub xs =>
       cases xs with
       | nil => exact rs_lift _ env [] (panic env [])
       | cons ck xs =>
         cases xs with
         | nil => exact NND_Stage1Eval.body_returned V P F C a p pub ck env
         | cons x xs => exact rs_lift _ env [] (panic env [])

#print axioms returned
end NND_Stage1RefEval
