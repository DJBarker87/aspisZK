import Aeneas.Std
import Aeneas.Tactic.RustAttributes
import Aeneas.Data.Discriminant
open Aeneas Aeneas.Std Result ControlFlow Error
set_option autoImplicit false

namespace AspisR1Query31Transcript

/-- Exact source error cases used by the first-stop finish wrapper. -/
inductive aspis_core.transcript.QuerySampleError where
| BoundNotPowerOfTwo : Std.U32 → aspis_core.transcript.QuerySampleError
| CountExceedsBound : Std.Usize → Std.U32 → aspis_core.transcript.QuerySampleError
| DrawLimitExhausted : Std.Usize → Std.Usize → aspis_core.transcript.QuerySampleError

def aspis_core.transcript.QuerySampleError.read_discriminant
    (x : aspis_core.transcript.QuerySampleError) : Isize :=
  match x with
  | .BoundNotPowerOfTwo _ => 0#isize
  | .CountExceedsBound _ _ => 1#isize
  | .DrawLimitExhausted _ _ => 2#isize

instance _root_.AspisR1Query31Transcript.aspis_core.transcript.QuerySampleError.instDiscriminantNamed :
    Aeneas.Std.Discriminant aspis_core.transcript.QuerySampleError Isize where
  read_discriminant := aspis_core.transcript.QuerySampleError.read_discriminant

/-- Exact extracted source record needed by the scan bridge; excludes the
    generated external-type template and all unrelated extracted declarations. -/
structure aspis_core.r0_transcript.QueryScan where
  accepted : Array Std.U32 22#usize
  accepted_len : Std.Usize
  draws : Std.Usize

end AspisR1Query31Transcript
