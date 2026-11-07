import NNG_EmittedContext
import OraclePortStdBuilder
set_option autoImplicit false
namespace AspisR1.NNG_StdArray
open Aeneas Aeneas.Std Result NNG_verify_finish
/-- Reuse the existing std builder, preserving mutable closure state and every
stopped callback. The abandoned independent transcription is .pending only. -/
abbrev fromFn := @OraclePortStdBuilder.fromFn
end AspisR1.NNG_StdArray
