import NEA_LineTail
set_option autoImplicit false
namespace NEA_LinePrimitive
open Aeneas Aeneas.Std Result

theorem double_value (x : U32) (canonical : x.val<2147483647) :
    ∃ d, AspisR1Qm31ArithmeticProbe.field.M31.double x=ok d ∧
      d.val<2147483647 ∧
      d.val=(if x.val+x.val >= 2147483647 then x.val+x.val-2147483647 else x.val+x.val) := by
  obtain ⟨d,run,value,cd⟩ := AspisR1.ExtractedCurrentM31AddSub.current_add_mod x x canonical canonical
  refine ⟨d,?_,cd,?_⟩
  · simpa only [AspisR1Qm31ArithmeticProbe.field.M31.double] using run
  · rw [value]
    change (x.val+x.val)%2147483647 = _
    split <;> omega

theorem sub_one_value (x : U32) (canonical : x.val<2147483647) :
    ∃ z, AspisR1Qm31ArithmeticProbe.field.M31.sub x 1#u32=ok z ∧
      z.val<2147483647 ∧ z.val=(if x.val >= 1 then x.val-1 else 2147483646) := by
  obtain ⟨z,run,value,cz⟩ := AspisR1.ExtractedCurrentM31AddSub.current_sub_mod x 1#u32 canonical (by decide)
  refine ⟨z,run,cz,?_⟩
  rw [value]
  change (x.val+2147483647-1)%2147483647 = _
  split <;> omega

#print axioms double_value
#print axioms sub_one_value
end NEA_LinePrimitive
