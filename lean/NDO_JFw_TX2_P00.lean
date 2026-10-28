import NDO_JFw_TX2_PowersExplicit
set_option autoImplicit false
noncomputable section
namespace AspisR1.JFw_TX2_P00
open Aeneas Aeneas.Std Result JFw_TX2_PowersExplicit
def value : E := ⟨⟨⟨1#u32,0#u32⟩,⟨0#u32,0#u32⟩⟩,⟨⟨0#u32,0#u32⟩,⟨0#u32,0#u32⟩⟩⟩
theorem canonical : FIo_WideValues.Canon value := by
  change ((1<2147483647 ∧ 0<2147483647) ∧ (0<2147483647 ∧ 0<2147483647)) ∧
    ((0<2147483647 ∧ 0<2147483647) ∧ (0<2147483647 ∧ 0<2147483647))
  omega
theorem meaning : decode value=decode gamma^0 := by
  change (1 : AspisWideTower.WideExact)=_ ^ 0
  rw [pow_zero]
theorem source : entry 0=value := identify 0 value canonical meaning
#print axioms canonical
#print axioms meaning
#print axioms source
end AspisR1.JFw_TX2_P00
end
