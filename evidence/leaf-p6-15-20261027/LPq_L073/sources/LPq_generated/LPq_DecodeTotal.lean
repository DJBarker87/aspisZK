import LPq_ReadPorts
set_option autoImplicit false
namespace AspisR1.LPq_DecodeTotal
open Aeneas Aeneas.Std Result LPi_FieldValues

theorem limbs (a : Array U32 8#usize)
    (hc : ∀ i, ∀ h : i<a.val.length, (a.val[i]'h).val<2147483647) :
    ∃ out, FIo_Native.aspis_core.field.wide_exact.WideExact.from_limbs a=ok (some out) ∧ canonE out := by
  have len : a.val.length=8 := a.property
  have r0 := XRy_ArrayRead.read a 0#usize (by decide)
  have c0 := hc 0 (by omega)
  have g0 : ¬ a.val[0] ≥ 2147483647#u32 := by scalar_tac
  have r1 := XRy_ArrayRead.read a 1#usize (by decide)
  have c1 := hc 1 (by omega)
  have g1 : ¬ a.val[1] ≥ 2147483647#u32 := by scalar_tac
  have r2 := XRy_ArrayRead.read a 2#usize (by decide)
  have c2 := hc 2 (by omega)
  have g2 : ¬ a.val[2] ≥ 2147483647#u32 := by scalar_tac
  have r3 := XRy_ArrayRead.read a 3#usize (by decide)
  have c3 := hc 3 (by omega)
  have g3 : ¬ a.val[3] ≥ 2147483647#u32 := by scalar_tac
  have r4 := XRy_ArrayRead.read a 4#usize (by decide)
  have c4 := hc 4 (by omega)
  have g4 : ¬ a.val[4] ≥ 2147483647#u32 := by scalar_tac
  have r5 := XRy_ArrayRead.read a 5#usize (by decide)
  have c5 := hc 5 (by omega)
  have g5 : ¬ a.val[5] ≥ 2147483647#u32 := by scalar_tac
  have r6 := XRy_ArrayRead.read a 6#usize (by decide)
  have c6 := hc 6 (by omega)
  have g6 : ¬ a.val[6] ≥ 2147483647#u32 := by scalar_tac
  have r7 := XRy_ArrayRead.read a 7#usize (by decide)
  have c7 := hc 7 (by omega)
  have g7 : ¬ a.val[7] ≥ 2147483647#u32 := by scalar_tac
  refine ⟨⟨⟨⟨a.val[0],a.val[1]⟩,⟨a.val[2],a.val[3]⟩⟩,⟨⟨a.val[4],a.val[5]⟩,⟨a.val[6],a.val[7]⟩⟩⟩,?_,⟨⟨⟨c0,c1⟩,⟨c2,c3⟩⟩,⟨⟨c4,c5⟩,⟨c6,c7⟩⟩⟩⟩
  simp only [FIo_Native.aspis_core.field.wide_exact.WideExact.from_limbs,
    FIo_Native.aspis_core.field.P,UScalar.ofNatCore_val_eq,bind_tc_ok,r0,g0,r1,g1,r2,g2,r3,g3,r4,g4,r5,g5,r6,g6,r7,g7,↓reduceIte]

#print axioms limbs
end AspisR1.LPq_DecodeTotal
