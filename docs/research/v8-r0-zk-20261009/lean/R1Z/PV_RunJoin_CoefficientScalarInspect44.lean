import R1Z.ProverRwSuccessCoefficientsSource
import R1Z.PV_CB3_WeightsMachineRow
set_option autoImplicit false
open Aeneas Aeneas.Std
#synth HShiftRight Usize Usize (Result Usize)
#synth HShiftLeft Usize Usize (Result Usize)
#print core.iter.range.UScalarStep
#print Aeneas.Std.instHShiftRightUScalarResult
#print Aeneas.Std.instHShiftLeftUScalarResult
