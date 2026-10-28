import NCP_EncodeExtracted.Funs
import NCP_DecodeReference
set_option autoImplicit false
noncomputable section
namespace NCP_EncodeStep
open Aeneas Aeneas.Std Result ControlFlow

theorem body (d : Array U32 8#usize) (out : Array U8 32#usize) (i : Usize)
    (bound : i.val < 8) :
    NCP_EncodeExtracted.NCP_refs.NCP_ref_encode_loop.body d out i =
      ok (.cont (out.setSlice! (4*i.val)
        (core.num.U32.to_le_bytes
          (d.val[i.val]'(by have := d.property; scalar_tac))).val,
        Usize.ofNatCore (i.val+1) (by scalar_tac))) := by
  unfold NCP_EncodeExtracted.NCP_refs.NCP_ref_encode_loop.body
  step*
  all_goals try scalar_tac
  all_goals simp [Array.setSlice!,List.setSlice!,core.num.U32.to_le_bytes,BitVec.toLEBytes]

#print axioms body
end NCP_EncodeStep
