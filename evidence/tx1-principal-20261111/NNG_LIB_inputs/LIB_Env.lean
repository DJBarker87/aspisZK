import LIB_Carriers
import NNC_ResumeEvents
import RSL_Pool
set_option autoImplicit false
namespace LIB_Env
open Aeneas Aeneas.Std
/-- Inverse fixed-byte carrier; no digest value is computed or postulated. -/
def nativeKey (b : RSL.B32) : Aeneas.Std.Array U8 32#usize :=
  ⟨LIB_Carriers.rawBytes b.bytes, by
    change (LIB_Carriers.rawBytes b.bytes).length = 32
    simpa only [NNC_ByteCarriers.nativeList, List.length_map] using b.len⟩
theorem key_roundtrip (b : RSL.B32) : LIB_Carriers.b32 (nativeKey b) = b := by
  cases b with
  | mk bs h =>
    change RSL.B32.mk _ _ = RSL.B32.mk bs h
    congr 1
    exact NNC_ByteCarriers.host_native bs
/-- A returned runtime digest, instantiated at the SAME partitioned input. -/
def hashv (env : RSL.Env) (parts : Slice (Slice U8)) :
    Result (Aeneas.Std.Array U8 32#usize) :=
  .ok (nativeKey (env.sha256 (NNC_ResumeEvents.parts parts)))
def digest (parts : List RSL.Bytes) : RSL.Spec RSL.B32 :=
  fun env o => o = ⟨.ret (env.sha256 parts), [.digest parts (env.sha256 parts)]⟩
theorem hashv_value (env : RSL.Env) (parts : Slice (Slice U8)) :
    hashv env parts = .ok (nativeKey (env.sha256 (NNC_ResumeEvents.parts parts))) := rfl
theorem digest_event (env : RSL.Env) (parts : Slice (Slice U8)) :
    NNC_ResumeEvents.digest (nativeKey (env.sha256 (NNC_ResumeEvents.parts parts))) =
    env.sha256 (NNC_ResumeEvents.parts parts) := key_roundtrip _
theorem digest_returns (parts : List RSL.Bytes) (env : RSL.Env) :
    NND_Returned.Returns (digest parts) env (env.sha256 parts) :=
  LIB_Carriers.graph_returns _ _ env
/-- PDA and Clock retain the complete reply, including rejection. -/
def pda := RSL.pdaCall
def clock : RSL.Spec (Except RSL.ProgramError UInt64) :=
  fun env o => o = ⟨.ret env.clock, [.clock env.clock]⟩
theorem pda_returns (seeds : List RSL.Bytes) (program : RSL.B32) (env : RSL.Env) :
    NND_Returned.Returns (pda seeds program) env (env.pda seeds program) := by
  apply NND_Returned.bind _ _ env _ _ (NND_Returned.environment env _)
  exact NND_Returned.bind _ _ env () _ (NND_Returned.emit env _)
    (NND_Returned.pure env _)
theorem clock_returns (env : RSL.Env) :
    NND_Returned.Returns clock env env.clock := LIB_Carriers.graph_returns _ _ env
/-- Fallible heap reservation reads the headline-bound runtime reply. -/
def reservation : RSL.Spec Bool := RSL.Spec.tryReserve
theorem reservation_returns (env : RSL.Env) :
    NND_Returned.Returns reservation env env.reservation :=
  NND_Returned.environment env RSL.Env.reservation
theorem reservation_functional : RSL.Spec.Functional reservation :=
  RSL.Spec.tryReserve_functional
#print axioms reservation_returns
#print axioms reservation_functional
#print axioms key_roundtrip
#print axioms hashv_value
#print axioms digest_event
#print axioms digest_returns
#print axioms pda_returns
#print axioms clock_returns
end LIB_Env
