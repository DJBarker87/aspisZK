import RPu_JFs_TX2_FromLimbs
set_option autoImplicit false
noncomputable section
namespace AspisR1.JFv_TX2_FromLimbsMeaning
open Aeneas Aeneas.Std Result JFs_TX2_Eight

def limbs (x : FIo_Install.NE) : Array U32 8#usize :=
  pack x.c0.c0.a x.c0.c0.b x.c0.c1.a x.c0.c1.b x.c1.c0.a x.c1.c0.b x.c1.c1.a x.c1.c1.b

theorem source (a : Array U32 8#usize) (out : FIo_Install.NE)
    (run : FIo_Native.aspis_core.field.wide_exact.WideExact.from_limbs a=ok (some out)) :
    limbs out=a := by
  obtain ⟨a0,a1,a2,a3,a4,a5,a6,a7,rfl⟩ := JFs_TX2_ArrayEight.shape a
  have r0 : Array.index_usize (pack a0 a1 a2 a3 a4 a5 a6 a7) 0#usize=ok a0 := rfl
  have r1 : Array.index_usize (pack a0 a1 a2 a3 a4 a5 a6 a7) 1#usize=ok a1 := rfl
  have r2 : Array.index_usize (pack a0 a1 a2 a3 a4 a5 a6 a7) 2#usize=ok a2 := rfl
  have r3 : Array.index_usize (pack a0 a1 a2 a3 a4 a5 a6 a7) 3#usize=ok a3 := rfl
  have r4 : Array.index_usize (pack a0 a1 a2 a3 a4 a5 a6 a7) 4#usize=ok a4 := rfl
  have r5 : Array.index_usize (pack a0 a1 a2 a3 a4 a5 a6 a7) 5#usize=ok a5 := rfl
  have r6 : Array.index_usize (pack a0 a1 a2 a3 a4 a5 a6 a7) 6#usize=ok a6 := rfl
  have r7 : Array.index_usize (pack a0 a1 a2 a3 a4 a5 a6 a7) 7#usize=ok a7 := rfl
  unfold FIo_Native.aspis_core.field.wide_exact.WideExact.from_limbs at run
  simp only [r0,r1,r2,r3,r4,r5,r6,r7,bind_tc_ok] at run
  split at run
  · cases run
  split at run
  · cases run
  split at run
  · cases run
  split at run
  · cases run
  split at run
  · cases run
  split at run
  · cases run
  split at run
  · cases run
  split at run
  · cases run
  have same : (⟨⟨⟨a0,a1⟩,⟨a2,a3⟩⟩,⟨⟨a4,a5⟩,⟨a6,a7⟩⟩⟩ : FIo_Install.NE)=out :=
    Option.some.inj (Result.ok.inj run)
  subst out
  rfl
#print axioms source
end AspisR1.JFv_TX2_FromLimbsMeaning
end
