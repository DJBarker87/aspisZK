import R1Z.PV_RunJoin_SemanticRowBound62
import R1Z.ProverRw19LoopBind
set_option autoImplicit false
namespace R1Z.PV_RunJoin_SemanticLoopBound62
open Aeneas Aeneas.Std Result ProverRwFull PV_RunJoin_ResultPost41
variable [ExternalTypes] [ExternalFuns]

theorem loop (logical : Slice U8) (bound : Nat) (small : logical.length≤bound)
    (n : Nat) (count row : U8) (out : alloc.vec.Vec U8) (at1 : Usize)
    (rank : row.val+n=count.val) (room : out.length+2*bound*n≤Usize.max) :
    Post (fun pair => pair.2.length≤out.length+2*bound*n)
      (host_compact.compact_semantic_loop logical out count at1 row) := by
  induction n generalizing row out at1 with
  | zero =>
    have stop : ¬ row<count := by change ¬row.val<count.val;omega
    unfold host_compact.compact_semantic_loop
    rw [ProverRw19LoopBind.loop_bind]
    simp only [host_compact.compact_semantic_loop.body,stop,if_false]
    split <;> change out.length≤out.length+2*bound*0 <;> omega
  | succ n ih =>
    have more : row<count := by change row.val<count.val;omega
    have nextrow : (U8.wrapping_add row 1#u8).val=row.val+1 := by
      rw [U8.wrapping_add_val_eq]
      change (row.val+1)%256=row.val+1
      apply Nat.mod_eq_of_lt
      have hc := count.hSize
      change count.val<256 at hc
      omega
    have remainingRoom : out.length+2*bound≤Usize.max := by
      simp only [Nat.mul_add,Nat.mul_one] at room
      omega
    unfold host_compact.compact_semantic_loop
    rw [ProverRw19LoopBind.loop_bind]
    simp only [host_compact.compact_semantic_loop.body,more,if_true]
    rw [bind_assoc_eq]
    apply PV_RunJoin_PostBind62.bind _ _ _ _
      (PV_RunJoin_SemanticRowBound62.row logical out row at1 bound small remainingRoom)
    rintro ⟨status,next⟩ nextBound
    dsimp only [Aeneas.Std.uncurry]
    cases status with
    | Err e =>
      simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok]
      apply PV_RunJoin_ResultPost41.bind
      intro ignored
      simp only [bind_tc_ok]
      change next.length≤out.length+2*bound*(n+1)
      simp only [Nat.mul_add,Nat.mul_one]
      omega
    | Ok pos =>
      simp only [core.result.Result.Insts.CoreOpsTry.branch,lift,bind_tc_ok]
      have tailRoom : next.length+2*bound*n≤Usize.max := by
        simp only [Nat.mul_add,Nat.mul_one] at room
        omega
      have h := ih (U8.wrapping_add row 1#u8) next pos (by rw [nextrow];omega) tailRoom
      cases he : host_compact.compact_semantic_loop logical next count pos (U8.wrapping_add row 1#u8) with
      | fail e => trivial
      | div => trivial
      | ok pair =>
        rw [he] at h
        change pair.2.length≤out.length+2*bound*(n+1)
        change pair.2.length≤next.length+2*bound*n at h
        simp only [Nat.mul_add,Nat.mul_one]
        omega

#print axioms loop
end R1Z.PV_RunJoin_SemanticLoopBound62
