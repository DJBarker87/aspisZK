import NND_PoolReturned
set_option autoImplicit false
namespace NNH_ReturnedClone
open RSL NND_Returned

theorem ofCloned {α : Type} (env : Env) (x : Except ProgramError α) :
 Returns (RS.ofCloned x) env x := by
 cases x with
 | ok a => exact rs_pure env a
 | error e =>
   simp only [RS.ofCloned]
   split
   · exact rs_bind _ _ env (.ok ()) (fun _ => .error e)
      (rs_lift _ env () (alloc env)) (fun _ => throw env e)
   · exact throw env e

theorem allocIf (env : Env) (b : Bool) : Returns (Spec.allocIf b) env () := by
 cases b
 · exact pure env ()
 · exact alloc env

def checkpointValue (a : OwnedAccount) (program : B32) (writable : Bool) : Except ProgramError Unit :=
 if decide (a.owner ≠ program) || a.is_signer || a.executable || a.is_writable != writable then
  .error .invalidAccountData
 else ebind a.length (fun n => echeck (n != CHECKPOINT_BYTES) .invalidAccountData)

theorem checkpoint_returned (env : Env) (a : OwnedAccount) (program : B32) (writable : Bool) :
 Returns (verifierCheckpoint a program writable) env (checkpointValue a program writable) := by
 unfold verifierCheckpoint checkpointValue
 split
 · exact throw env _
 · exact rs_bind _ _ env _ _ (ofCloned env a.length) (fun n => check env _ _)

#print axioms ofCloned
#print axioms allocIf
#print axioms checkpoint_returned
end NNH_ReturnedClone
