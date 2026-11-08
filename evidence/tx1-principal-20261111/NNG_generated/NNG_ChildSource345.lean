import NNG_Image328
import NNG_PE345
import NMT_345First_T5
import NMT_345Prep_T5
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNG_ChildSource345
open Aeneas Aeneas.Std Result NMT_345

def native (pub : Public) (publicBytes proof : Slice U8) (k : Usize) : NNG_Native328.Args :=
 ⟨NMT_345First.toT5 pub,publicBytes,proof,k⟩
def args (pub : Public) (publicBytes proof : Slice U8) (k : Usize) :=
 NNG_Native328.args (native pub publicBytes proof k)
def reply : core.result.Result (alloc.vec.Vec U8) NMT_first.solana_program_error.ProgramError → core.result.Result (alloc.vec.Vec U8) PE
 | .Ok b=>.Ok b | .Err e=>.Err (NNG_PE345.fromFirst e)
def port : core.result.Result (alloc.vec.Vec U8) PE → Except RSL.ProgramError RSL.Bytes :=
 rustResult (fun b=>LIB_Carriers.bytes b.deref)
def call (env : RSL.Env) (pub : Public) (publicBytes proof : Slice U8) (k : Usize) : Result Ret :=
 NMP_ResultTransport.outer reply (NNG_Native328.body (native pub publicBytes proof k) env)
def events (env : RSL.Env) (pub : Public) (publicBytes proof : Slice U8) (k : Usize) :=
 (NNG_Producer328.producer (args pub publicBytes proof k) env).events

theorem args_fields (pub : Public) (publicBytes proof : Slice U8) (k : Usize) :
 args pub publicBytes proof k=
 ⟨NMT_345Prep.toT5 pub,LIB_Carriers.bytes publicBytes,LIB_Carriers.bytes proof,k.val⟩ := by
 unfold args native NNG_Native328.args NNG_Carriers328.toPublic
 rw [NMT_345First.toT5_inverse]
#print axioms args_fields

theorem reply_port (r : core.result.Result (alloc.vec.Vec U8) NMT_first.solana_program_error.ProgramError) :
 port (reply r)=NNG_Carriers328.port r := by
 cases r with
 | Ok b=>rfl
 | Err e=>exact congrArg Except.error (NNG_PE345.source e)
#print axioms reply_port

/-- Actual emitted328 result plus its exact source chronology, at345's SAME
native public/public-bytes/proof/k call. No child or endpoint parameter. -/
theorem observation (env : RSL.Env) (pub : Public) (publicBytes proof : Slice U8) (k : Usize)
 (bound : k.val≤UScalar.cMax .Usize) :
 LIB_Carriers.resultObs port (events env pub publicBytes proof k) (call env pub publicBytes proof k)=
 NNG_Producer328.producer (args pub publicBytes proof k) env := by
 unfold call
 calc
  _=LIB_Carriers.resultObs NNG_Carriers328.port (events env pub publicBytes proof k)
   (NNG_Native328.body (native pub publicBytes proof k) env) :=
    NNG_StateCalls094.obs_outer reply port NNG_Carriers328.port reply_port _ _
  _=_ := by
   unfold events args NNG_Producer328.producer
   rw [NNG_Image328.roundtrip _ bound]
   dsimp only
   generalize NNG_Native328.body (native pub publicBytes proof k) env=r
   cases r <;> rfl
#print axioms observation
end AspisR1.NNG_ChildSource345
