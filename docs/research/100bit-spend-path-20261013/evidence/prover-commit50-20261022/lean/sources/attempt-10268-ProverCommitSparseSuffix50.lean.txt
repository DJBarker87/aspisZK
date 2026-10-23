import R1Z.ProverCommitSparsePredicate50
import R1Z.ProverCommitSparseAddress50
import R0P.LaneMap
/-! Entire owned suffix encoder equals the existing big-endian rowCode. -/
set_option autoImplicit false
namespace R1Z.ProverCommitSparseSuffix50
open Aeneas Aeneas.Std Result AspisR1ProducerRelease47
open ProverCommitPrimitive47 ProverCommitSubfieldOps47
open ProverCommitSparsePredicate50 (rawOne)

theorem append_val (x : Usize) (b : Bool) (hx : x.val<512) :
    ((core.num.Usize.wrapping_shl x 1#u32) ||| core.convert.num.FromUsizeBool.from b).val=Nat.bit b x.val := by
  let bv := core.convert.num.FromUsizeBool.from b
  have hb : bv.val=b.toNat := by cases b <;> rfl
  obtain ⟨z,hz,hzv,hzb⟩ := ProverCommitSparseAddress50.row x bv 1#u8 (by decide) hx
    (by rw [hb];cases b <;> decide)
  have he : ((core.num.Usize.wrapping_shl x 1#u32) ||| bv)=z := by
    apply Result.ok.inj
    exact hz
  rw [he,hzv,Nat.bit_val]
  change x.val*2+bv.val=2*x.val+b.toNat
  rw [hb,Nat.mul_comm x.val 2]

theorem suffix (p : Nat → Old.Q) (n : Nat) (left : U8) (hl : left.val=n)
    (start : Usize) (bound : start.val+n≤10) :
    ∃ z : Usize, sparse_scan50.suffix (ProverCommitQArray48.array 10#usize p) start left=ok z ∧
      z.val=R0P.rowCode n (fun i => rawOne (p (start.val+i.val))) ∧ z.val<2^n := by
  induction n generalizing left with
  | zero =>
    have hz : left=0#u8 := by scalar_tac
    refine ⟨0#usize,?_,rfl,?_⟩
    · rw [sparse_scan50.suffix,hz];rfl
    · change 0<1;omega
  | succ n ih =>
    have hz : left≠0#u8 := by scalar_tac
    have hdec : (U8.wrapping_sub left 1#u8).val=n := by
      rw [ProverCommitBasisCounter47.sub_one left (by omega)];omega
    obtain ⟨prev,hprev,hprevv,hprevb⟩ := ih _ hdec (by omega)
    let cast := core.convert.num.FromUsizeU8.from (U8.wrapping_sub left 1#u8)
    have hcast : cast.val=n := by scalar_tac
    have hidx : (core.num.Usize.wrapping_add start cast).val=start.val+n := by
      change (Usize.wrapping_add start cast).val=_
      rw [ProverCommitBasisFillValue47.add_val _ _ (by rw [hcast];omega),hcast]
    let z := (core.num.Usize.wrapping_shl prev 1#u32) ||| core.convert.num.FromUsizeBool.from (rawOne (p (start.val+n)))
    have hprevsmall : prev.val<512 := by
      have hp : 2^n≤2^9 := Nat.pow_le_pow_right (by decide) (by omega)
      omega
    have hval : z.val=R0P.rowCode (n+1) (fun i => rawOne (p (start.val+i.val))) := by
      rw [append_val prev _ hprevsmall,hprevv,R0P.rowCode]
      rfl
    refine ⟨z,?_,hval,?_⟩
    · rw [sparse_scan50.suffix]
      simp only [hz,if_false,lift,bind_tc_ok,hprev]
      rw [ProverCommitQArray48.index 10#usize p _ (by change _<10;rw [hidx];omega)]
      simp only [bind_tc_ok]
      rw [hidx,ProverCommitSparsePredicate50.one_result]
      rfl
    · rw [hval]
      exact R0P.rowCode_lt _ _

#print axioms append_val
#print axioms suffix
end R1Z.ProverCommitSparseSuffix50
