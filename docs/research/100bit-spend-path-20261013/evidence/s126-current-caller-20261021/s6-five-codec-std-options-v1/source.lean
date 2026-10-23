import S6FiveCodecNativeV1
import S6StdOptionSourceV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisS6FiveUnrolledCodec.StdOptions
abbrev SliceArrayEq := {T U : Type} → {N : Usize} →
  core.cmp.PartialEq T U → Slice T → Array U N → Result Bool

/-- Install the actual extracted generic Option methods. Only the slice/array
standard-library comparison remains a boundary. -/
def ops (sliceArrayEq : SliceArrayEq) : Ops where
  sliceArrayEq := sliceArrayEq
  optionOkOr := AspisS6StdOptionMethods.option_ok_or
  optionEq := AspisS6StdOptionMethods.option_eq

def encode (sliceArrayEq : SliceArrayEq)
    (statement : aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalStatementV1) :=
  AspisS6FiveUnrolledCodec.encode (ops sliceArrayEq) statement

def decode (sliceArrayEq : SliceArrayEq) (bytes : Slice U8) :=
  AspisS6FiveUnrolledCodec.decode (ops sliceArrayEq) bytes

#print axioms ops
#print axioms encode
#print axioms decode
end AspisS6FiveUnrolledCodec.StdOptions
