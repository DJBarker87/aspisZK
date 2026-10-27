import FJf_EbyKCodec
import FIo_FromLimbs
set_option autoImplicit false
namespace AspisR1.FJf_FromLimbsPacked
open Aeneas Aeneas.Std Result
open FIo_FieldBridge (NE)
theorem value (a b c d e f g h : U32) (out : NE)
    (run : FIo_Native.aspis_core.field.wide_exact.WideExact.from_limbs
      (Array.make 8#usize [a,b,c,d,e,f,g,h])=ok (some out)) :
    out=⟨⟨⟨a,b⟩,⟨c,d⟩⟩,⟨⟨e,f⟩,⟨g,h⟩⟩⟩ := by
  have r0 : Array.index_usize (Array.make 8#usize [a,b,c,d,e,f,g,h]) 0#usize=ok a := rfl
  have r1 : Array.index_usize (Array.make 8#usize [a,b,c,d,e,f,g,h]) 1#usize=ok b := rfl
  have r2 : Array.index_usize (Array.make 8#usize [a,b,c,d,e,f,g,h]) 2#usize=ok c := rfl
  have r3 : Array.index_usize (Array.make 8#usize [a,b,c,d,e,f,g,h]) 3#usize=ok d := rfl
  have r4 : Array.index_usize (Array.make 8#usize [a,b,c,d,e,f,g,h]) 4#usize=ok e := rfl
  have r5 : Array.index_usize (Array.make 8#usize [a,b,c,d,e,f,g,h]) 5#usize=ok f := rfl
  have r6 : Array.index_usize (Array.make 8#usize [a,b,c,d,e,f,g,h]) 6#usize=ok g := rfl
  have r7 : Array.index_usize (Array.make 8#usize [a,b,c,d,e,f,g,h]) 7#usize=ok h := rfl
  unfold FIo_Native.aspis_core.field.wide_exact.WideExact.from_limbs at run
  simp only [r0,r1,r2,r3,r4,r5,r6,r7,bind_tc_ok] at run
  repeat' first
  | (solve | cases run)
  | split at run
  all_goals exact (Option.some.inj (Result.ok.inj run)).symm
#print axioms value
end AspisR1.FJf_FromLimbsPacked
