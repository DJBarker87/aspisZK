import NDO_JFw_Frames
set_option autoImplicit false
namespace AspisR1.JGe_WindowAssembly
open Aeneas Aeneas.Std
attribute [local irreducible] JFx_NativeBytes.proof

def chunks (width : Nat) : Nat → Nat → List (List U8)
  | 0,_ => []
  | n+1,off => (JFw_Frames.window off width).val :: chunks width n (off+width)

theorem split (off n m : Nat) :
    (JFw_Frames.window off (n+m)).val=
      (JFw_Frames.window off n).val ++ (JFw_Frames.window (off+n) m).val := by
  simp only [JFw_Frames.window,List.take_add,List.drop_drop,Nat.add_comm]
#print axioms split

theorem source (width n off : Nat) :
    (JFw_Frames.window off (width*n)).val=(chunks width n off).flatten := by
  induction n generalizing off with
  | zero => simp only [Nat.mul_zero,JFw_Frames.window,List.take_zero,chunks,List.flatten_nil]
  | succ n ih =>
    rw [show width*(n+1)=width+width*n by rw [Nat.mul_succ,Nat.add_comm],split,ih]
    rfl
#print axioms source
end AspisR1.JGe_WindowAssembly
