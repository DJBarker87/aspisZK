import R1Z.ProverRwSuccessEquality
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverRwSuccessWireSource
open Aeneas Aeneas.Std Result ControlFlow Error ProverRwFull
def r1_wire.DOMAIN : Slice Std.U8 :=
  Array.to_slice
    (Array.make 38#usize [
      85#u8, 78#u8, 80#u8, 82#u8, 79#u8, 86#u8, 69#u8, 68#u8, 58#u8, 82#u8,
      49#u8, 58#u8, 80#u8, 82#u8, 73#u8, 86#u8, 65#u8, 84#u8, 69#u8, 45#u8,
      83#u8, 65#u8, 76#u8, 84#u8, 69#u8, 68#u8, 58#u8, 83#u8, 69#u8, 77#u8,
      65#u8, 78#u8, 84#u8, 73#u8, 67#u8, 58#u8, 80#u8, 51#u8
      ])
end R1Z.ProverRwSuccessWireSource
