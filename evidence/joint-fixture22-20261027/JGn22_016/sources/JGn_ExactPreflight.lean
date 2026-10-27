import JGn_ExactEval
import JGl_NumericData
import FIq_Native13
set_option autoImplicit false
namespace AspisR1.JGn_ExactPreflight
open Aeneas Aeneas.Std Result FIq_Native

theorem add : field.QM31.add
    ⟨⟨1#u32,2#u32⟩,⟨3#u32,4#u32⟩⟩ ⟨⟨4#u32,3#u32⟩,⟨2#u32,1#u32⟩⟩=
    ok ⟨⟨5#u32,5#u32⟩,⟨5#u32,5#u32⟩⟩ := by jgn_eval
#print axioms add

theorem product : field.QM31.mul
    ⟨⟨60053925#u32,1891194216#u32⟩,⟨2090430923#u32,260852809#u32⟩⟩
    ⟨⟨839969315#u32,1393507838#u32⟩,⟨1451026085#u32,492151165#u32⟩⟩=
    ok ⟨⟨1458369550#u32,1316359454#u32⟩,⟨1385711809#u32,768552005#u32⟩⟩ := by jgn_eval
#print axioms product

theorem loop : pool_v1.pair_forest_copy_terminal.pattern_values_literal_loop0
    field.QM31.ONE (Array.repeat 16#usize field.QM31.ZERO) field.QM31.ONE 15#usize=
    ok (⟨[field.QM31.ZERO,field.QM31.ZERO,field.QM31.ZERO,field.QM31.ZERO,
      field.QM31.ZERO,field.QM31.ZERO,field.QM31.ZERO,field.QM31.ZERO,
      field.QM31.ZERO,field.QM31.ZERO,field.QM31.ZERO,field.QM31.ZERO,
      field.QM31.ZERO,field.QM31.ZERO,field.QM31.ZERO,field.QM31.ONE],by rfl⟩,16#usize) := by
  jgn_eval
#print axioms loop
end AspisR1.JGn_ExactPreflight
