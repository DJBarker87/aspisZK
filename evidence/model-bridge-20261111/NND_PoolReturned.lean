import NND_Returned
import RSL_Pool
set_option autoImplicit false
namespace NND_Returned
open RSL

def option {α : Type} (x : Option α) (e : ProgramError) : Except ProgramError α :=
 match x with | some a => .ok a | none => .error e

def eseq {α : Type} (x : Except ProgramError Unit) (y : Except ProgramError α) : Except ProgramError α :=
 ebind x (fun _ => y)

def echeck (b : Bool) (e : ProgramError) : Except ProgramError Unit :=
 if b then .error e else .ok ()

theorem seq {α : Type} (m : RS Unit) (k : RS α) (env : Env)
 (x : Except ProgramError Unit) (y : Except ProgramError α)
 (hm : Returns m env x) (hk : Returns k env y) :
 Returns (RS.seq m k) env (eseq x y) := rs_bind m (fun _ => k) env x (fun _ => y) hm (fun _ => hk)

theorem pda (env : Env) (seeds : List Bytes) (program : B32) :
 Returns (pdaCall seeds program) env (env.pda seeds program) :=
 bind _ _ env _ _ (environment env _) (bind _ _ env _ _ (emit env _) (pure env _))

theorem pdaOrErr (env : Env) (seeds : List Bytes) (program : B32) :
 Returns (RSL.pdaOrErr seeds program) env (option (env.pda seeds program) .invalidAccountData) := by
 unfold RSL.pdaOrErr
 have h := rs_bind _ _ env _ (fun x => option x .invalidAccountData)
  (rs_lift _ env _ (pda env seeds program)) (fun x => ofOption env x .invalidAccountData)
 exact h

theorem masterBox (L : PoolLib) (env : Env) (b : Bytes) :
 Returns (decodeMasterBox L b) env (option (L.decodeMaster b) .invalidAccountData) := by
 unfold decodeMasterBox
 have h := rs_bind _ _ env _ (fun m => Except.ok m)
  (ofOption env (L.decodeMaster b) .invalidAccountData)
  (fun m => rs_bind _ _ env _ (fun _ => Except.ok m) (rs_lift _ env _ (alloc env))
    (fun _ => rs_pure env m))
 cases hd : L.decodeMaster b <;> simpa [option,ebind,hd] using h

theorem checkpointBox (L : PoolLib) (env : Env) (b : Bytes) :
 Returns (decodeCheckpointBox L b) env (option (L.decodeCheckpoint b) .invalidAccountData) := by
 unfold decodeCheckpointBox
 have h := rs_bind _ _ env _ (fun c => Except.ok c)
  (ofOption env (L.decodeCheckpoint b) .invalidAccountData)
  (fun c => rs_bind _ _ env _ (fun _ => Except.ok c) (rs_lift _ env _ (alloc env))
    (fun _ => rs_pure env c))
 cases hd : L.decodeCheckpoint b <;> simpa [option,ebind,hd] using h

#print axioms seq
#print axioms pda
#print axioms pdaOrErr
#print axioms masterBox
#print axioms checkpointBox
end NND_Returned
