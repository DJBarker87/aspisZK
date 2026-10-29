import R1Z.PV_RunJoin_GammaSourceCell50
import R1Z.PV_RunJoin_PrefixFold50
set_option autoImplicit false
namespace R1Z.PV_RunJoin_GammaSourceFill50
open Aeneas Aeneas.Std Result AspisR1ProducerRelease47
open ProverCommitWideOps48
open PV_RunJoin_GammaSourceCell50 (Columns)

theorem complete (c : Columns) (powers : Array Source 29#usize)
    (n : Nat) (left : U16) (hl : left.val=n) (out : Array Source 1024#usize)
    (row : Usize) (bound : row.val+n≤1024) :
    gamma53.fill c powers out row left=PV_RunJoin_PrefixFold50.arrayRun
      (fun j => gamma53.cell c powers j 0#usize 29#u8 field.wide_exact.WideExact.ZERO) n out row := by
  induction n generalizing left out row with
  | zero =>
    have hz : left=0#u16 := by scalar_tac
    rw [gamma53.fill,hz]
    rfl
  | succ n ih =>
    have hn : left≠0#u16 := by scalar_tac
    have dec : (U16.wrapping_sub left 1#u16).val=n := by
      rw [ProverCommitPairCounter47.sub_one left (by omega)];omega
    have inc : (Usize.wrapping_add row 1#usize).val=row.val+1 :=
      ProverCommitPairCounter47.next_val row (by omega)
    rw [gamma53.fill]
    simp only [hn,if_false,PV_RunJoin_PrefixFold50.arrayRun,lift,bind_tc_ok]
    apply congrArg (Aeneas.Std.bind _)
    funext value
    apply congrArg (Aeneas.Std.bind _)
    funext next
    simp only [lift,bind_tc_ok]
    exact ih _ dec next _ (by rw [inc];omega)
#print axioms complete
end R1Z.PV_RunJoin_GammaSourceFill50
