import GExq_RetainedReader
import GExp_RetainedReader
set_option autoImplicit false
namespace AspisR1.F3U_ReaderCode
open Aeneas Aeneas.Std

theorem same (reserved : Bool) (ck proof pub : Slice U8) (v : VTop_Stages.transport.Variant) :
    GExq_RetainedReader.code reserved ck proof pub v=GExp_RetainedReader.code reserved ck proof pub v := rfl

#print axioms same
end AspisR1.F3U_ReaderCode
