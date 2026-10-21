import CheckpointP6KBytes

set_option autoImplicit false
namespace AspisR1.CheckpointBytesScalar
open Aeneas Aeneas.Std Result
open OraclePortCkptAbi2Extracted
#print Aeneas.Std.UScalar.shiftRight
#print Aeneas.Std.UScalar.cast
#print Aeneas.Std.UScalar.div
#print Aeneas.Std.Array.index_usize
#print Aeneas.Std.Slice.index_usize
#print Aeneas.Std.UScalar.mul
#print Aeneas.Std.UScalar.rem
#print Aeneas.Std.UScalar.val
#print Aeneas.Std.UScalar.bv
set_option pp.all true in
#print OraclePortCkptAbi2Extracted.e_byte
set_option pp.all true in
#print OraclePortCkptAbi2Extracted.word_spec
end AspisR1.CheckpointBytesScalar
