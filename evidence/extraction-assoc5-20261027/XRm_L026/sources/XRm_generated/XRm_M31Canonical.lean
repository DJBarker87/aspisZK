import XRk_Field
open Aeneas Aeneas.Std Result
namespace XRm_M31Canonical
abbrev P : U32 := 2147483647#u32
theorem add (a b out : U32) (ha : a<P) (hb : b<P)
    (run : XRk_Field.field.M31.add a b=ok out) : out<P := by
  unfold XRk_Field.field.M31.add XRk_Field.field.P at run
  simp only [lift,bind_tc_ok] at run
  split at run <;> cases Result.ok.inj run <;> unfold P at * <;> scalar_tac

theorem sub (a b out : U32) (ha : a<P) (hb : b<P)
    (run : XRk_Field.field.M31.sub a b=ok out) : out<P := by
  unfold XRk_Field.field.M31.sub XRk_Field.field.P at run
  simp only [lift,bind_tc_ok] at run
  split at run <;> cases Result.ok.inj run <;> unfold P at * <;> scalar_tac
#print axioms add
#print axioms sub
end XRm_M31Canonical
