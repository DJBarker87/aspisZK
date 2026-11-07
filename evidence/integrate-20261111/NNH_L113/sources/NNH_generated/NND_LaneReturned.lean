import NND_PoolReturned
import RSL_TX2_217
set_option autoImplicit false
namespace NND_LaneReturned
open RSL NND_Returned
/-- Value only; the Box-allocation abort remains an observation of Ref. -/
def value (b : Bytes) : Except ProgramError LaneState :=
 option (TX2_217.laneDecode b) .invalidAccountData

theorem returned (b : Bytes) (env : Env) : Returns (TX2_217.Ref b) env (value b) := by
 unfold TX2_217.Ref value
 cases hd : TX2_217.laneDecode b with
 | none => exact throw env _
 | some lane =>
   exact rs_bind _ _ env _ (fun _ => .ok lane) (rs_lift _ env _ (alloc env)) (fun _ => rs_pure env lane)
#print axioms returned
end NND_LaneReturned
