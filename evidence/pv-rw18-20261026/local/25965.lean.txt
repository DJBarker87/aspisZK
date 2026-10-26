import R1Z.ProverCommitLimbBytes47
import Mathlib.Data.List.OfFn
set_option autoImplicit false
namespace R1Z.ProverRw18CodecGroups
open AspisR1.RetainedFieldByteCodec

theorem grouped (limbs : QM31Limbs) :
    List.ofFn (encodeQM31LE limbs)=
      (List.ofFn (fun i : Fin 4 => List.ofFn (encodeM31LE (limbs i)))).flatten := by
  rw [List.ofFn_mul (m := 4) (n := 4)]
  congr 1

#print axioms grouped
end R1Z.ProverRw18CodecGroups
