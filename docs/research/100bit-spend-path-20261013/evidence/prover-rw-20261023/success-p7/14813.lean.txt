import R1Z.ProverRwP7ReverseSource
import R1Z.ProverRwSuccessPowerTotal
set_option autoImplicit false
namespace R1Z.ProverRwP7ReverseControl
open Aeneas Aeneas.Std Result ControlFlow
abbrev Src := ProverRwP7ReverseSource.reverse32_loop

def nextX (x : U32) : U32 := U32.wrapping_shr x 1#u32
def nextOut (x out : U32) : U32 := (U32.wrapping_shl out 1#u32) ||| (x &&& 1#u32)
def finite : Nat → U32 → U32 → U32
  | 0, _, out => out
  | n+1, x, out => finite n (nextX x) (nextOut x out)

theorem unfold_source (x out : U32) (i : Usize) :
    Src x out i = (do
      let cf ← ProverRwP7ReverseSource.reverse32_loop.body x out i
      match cf with
      | .done result => ok result
      | .cont (a,b,k) => Src a b k) := by
  unfold Src ProverRwP7ReverseSource.reverse32_loop
  rw [ProverRwSuccessPowerTotal.loop_bind]
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro cf _
  cases cf with
  | done x => rfl
  | cont p => rcases p with ⟨a,b,k⟩; rfl

theorem loop_finite (fuel : Nat) (x out : U32) (i : Usize)
    (bound : i.val+fuel=32) : Src x out i = ok (finite fuel x out) := by
  induction fuel generalizing x out i with
  | zero =>
    have h : ¬i<32#usize := by change ¬i.val<32; omega
    rw [unfold_source]
    simp only [ProverRwP7ReverseSource.reverse32_loop.body,h,if_false,bind_tc_ok,finite]
  | succ fuel ih =>
    have h : i<32#usize := by change i.val<32; omega
    have step : (Usize.wrapping_add i 1#usize).val=i.val+1 := by
      rw [Usize.wrapping_add_val_eq]
      change (i.val+1)%UScalar.size .Usize=i.val+1
      apply Nat.mod_eq_of_lt
      have big := (32#usize).hSize
      change 32<UScalar.size .Usize at big
      omega
    rw [unfold_source]
    simp only [ProverRwP7ReverseSource.reverse32_loop.body,h,if_true,lift,bind_tc_ok]
    change Src (nextX x) (nextOut x out) (Usize.wrapping_add i 1#usize) = ok _
    exact ih _ _ _ (by omega)

theorem source (x : U32) :
    ProverRwP7ReverseSource.reverse32 x = ok (finite 32 x 0#u32) :=
  loop_finite 32 x 0#u32 0#usize rfl
#print axioms unfold_source
#print axioms loop_finite
#print axioms source
end R1Z.ProverRwP7ReverseControl
