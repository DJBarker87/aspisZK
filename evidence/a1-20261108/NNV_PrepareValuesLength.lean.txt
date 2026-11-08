import NNV_PrepareValuesOutput
import NNV_PrepareBufferLengths
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNV_PrepareValuesLength
open RSL NNH_Libraries

theorem returned (a : TX1_087.Args VL) (env : Env) (sem : Verified VL) (v : VL.View)
 (p : NNV_PrepareFrontCut.Packet a env sem v) : p.y1.length=928 := by
 rw [(NNV_PrepareValuesOutput.returned a env sem v p).2]
 change (List.map _ (List.ofFn _)).length = _
 rw [List.length_map,List.length_ofFn]
 have length := (NNV_PrepareBufferLengths.returned a env sem v p).2.2
 have bound : (p.logical.drop LOGICAL_SEMANTIC).length ≤ Usize.max := by rw [length];scalar_tac
 exact (LIBC_Bytes.raw_length _ bound).trans length
#print axioms returned
end AspisR1.NNV_PrepareValuesLength
end
