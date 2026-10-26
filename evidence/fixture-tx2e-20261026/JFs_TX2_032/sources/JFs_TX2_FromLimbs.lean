import JFs_TX2_Reduce
import JFs_TX2_ArrayEight
import FIo_FromLimbs
set_option autoImplicit false
noncomputable section
namespace AspisR1.JFs_TX2_FromLimbs
open Aeneas Aeneas.Std Result
open JFs_TX2_Eight
theorem packed (a0 a1 a2 a3 a4 a5 a6 a7 : U32)
    (hc : a0.val<2147483647 ∧ a1.val<2147483647 ∧ a2.val<2147483647 ∧ a3.val<2147483647 ∧ a4.val<2147483647 ∧ a5.val<2147483647 ∧ a6.val<2147483647 ∧ a7.val<2147483647) :
    ∃ out, FIo_Native.aspis_core.field.wide_exact.WideExact.from_limbs (pack a0 a1 a2 a3 a4 a5 a6 a7)=ok (some out) ∧
      FIo_WideValues.Canon out := by
  rcases hc with ⟨h0,h1,h2,h3,h4,h5,h6,h7⟩
  have r0 : Array.index_usize (pack a0 a1 a2 a3 a4 a5 a6 a7) 0#usize=ok a0 := rfl
  have b0 : ¬ a0≥FIo_Native.aspis_core.field.P := by unfold FIo_Native.aspis_core.field.P;scalar_tac
  have r1 : Array.index_usize (pack a0 a1 a2 a3 a4 a5 a6 a7) 1#usize=ok a1 := rfl
  have b1 : ¬ a1≥FIo_Native.aspis_core.field.P := by unfold FIo_Native.aspis_core.field.P;scalar_tac
  have r2 : Array.index_usize (pack a0 a1 a2 a3 a4 a5 a6 a7) 2#usize=ok a2 := rfl
  have b2 : ¬ a2≥FIo_Native.aspis_core.field.P := by unfold FIo_Native.aspis_core.field.P;scalar_tac
  have r3 : Array.index_usize (pack a0 a1 a2 a3 a4 a5 a6 a7) 3#usize=ok a3 := rfl
  have b3 : ¬ a3≥FIo_Native.aspis_core.field.P := by unfold FIo_Native.aspis_core.field.P;scalar_tac
  have r4 : Array.index_usize (pack a0 a1 a2 a3 a4 a5 a6 a7) 4#usize=ok a4 := rfl
  have b4 : ¬ a4≥FIo_Native.aspis_core.field.P := by unfold FIo_Native.aspis_core.field.P;scalar_tac
  have r5 : Array.index_usize (pack a0 a1 a2 a3 a4 a5 a6 a7) 5#usize=ok a5 := rfl
  have b5 : ¬ a5≥FIo_Native.aspis_core.field.P := by unfold FIo_Native.aspis_core.field.P;scalar_tac
  have r6 : Array.index_usize (pack a0 a1 a2 a3 a4 a5 a6 a7) 6#usize=ok a6 := rfl
  have b6 : ¬ a6≥FIo_Native.aspis_core.field.P := by unfold FIo_Native.aspis_core.field.P;scalar_tac
  have r7 : Array.index_usize (pack a0 a1 a2 a3 a4 a5 a6 a7) 7#usize=ok a7 := rfl
  have b7 : ¬ a7≥FIo_Native.aspis_core.field.P := by unfold FIo_Native.aspis_core.field.P;scalar_tac
  let out : FIo_Install.NE := ⟨⟨⟨a0,a1⟩,⟨a2,a3⟩⟩,⟨⟨a4,a5⟩,⟨a6,a7⟩⟩⟩
  have run : FIo_Native.aspis_core.field.wide_exact.WideExact.from_limbs (pack a0 a1 a2 a3 a4 a5 a6 a7)=ok (some out) := by
    simp only [FIo_Native.aspis_core.field.wide_exact.WideExact.from_limbs,r0,r1,r2,r3,r4,r5,r6,r7,if_neg b0,if_neg b1,if_neg b2,if_neg b3,if_neg b4,if_neg b5,if_neg b6,if_neg b7,bind_tc_ok,out]
  exact ⟨out,run,FIo_FromLimbs.canonical _ out run⟩

#print axioms packed
end AspisR1.JFs_TX2_FromLimbs
end
