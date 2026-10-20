import PaintBlocksPrefixV1
import ToBytesP6StepsV3
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1PaintSourceLimbsV1
open AspisR1WideToBytesSource P6ToBytes.Steps

def limbBlock (x : field.wide_exact.WideExact) (i : Nat) : List U8 :=
  (core.num.U32.to_le_bytes (sourceLimbs x)[i]!).val

theorem paint_eight_limbs_exact (x : field.wide_exact.WideExact) :
    AspisR1PaintBlocksPrefixV1.paint (limbBlock x) 4 8 (List.replicate 32 0#u8) =
      (sourceLimbs x).flatMap (fun w => (core.num.U32.to_le_bytes w).val) := by
  rw [AspisR1PaintBlocksPrefixV1.paint_full (limbBlock x) 4 8 _ (by rfl)
    (fun i _ => u32BytesLen _)]
  simp only [List.range_succ,List.range_zero,List.flatMap_append,List.flatMap_cons,
    List.flatMap_nil,List.append_nil,limbBlock,sourceLimbs,
    List.getElem!_cons_zero,List.getElem!_cons_succ,List.nil_append,List.append_assoc]

#print axioms paint_eight_limbs_exact
end AspisR1PaintSourceLimbsV1
