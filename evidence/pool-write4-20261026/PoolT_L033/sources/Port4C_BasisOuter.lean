import Port4C_BasisInner

/-! Native basis scheduling port. Only the primitive field leaves are named
session A dependencies; no native block/outer/basis equality is assumed. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.Port4C_BasisOuter
open Aeneas Aeneas.Std Result ControlFlow AspisR1Stage2 Port3_NativeQueryBody
open Port3_PushFrame (bind_success)
abbrev Basis := Array U32 256#usize

structure SessionABasis (ops : Ops) : Prop where
  s3_s4_mul : ops.op7=AspisR1Qm31ArithmeticProbe.field.M31.mul
  s3_s4_sub : ops.op6=AspisR1Qm31ArithmeticProbe.field.M31.sub
  s3_s4_double : ops.op8=S7Kani3BasisOuter.double
  zero : ops.op4=ok (0#u32)
  one : ops.op5=ok (1#u32)

theorem checked_mul (x y : Usize) (small : x.val*y.val≤4096) :
    (x*y : Result Usize)=ok (Usize.wrapping_mul x y) := by
  have capacity : 4096≤Usize.max := by scalar_tac
  have spec : WP.spec (x*y : Result Usize) (fun out => out.val=x.val*y.val) := by
    apply UScalar.mul_spec
    simpa only [UScalar.max_USize_eq] using small.trans capacity
  obtain ⟨out,run,value⟩ := WP.spec_imp_exists spec
  have same : out=Usize.wrapping_mul x y := by
    apply UScalar.eq_of_val_eq
    exact value.trans (Port3_Wrapping.wrap_mul_value x y small).symm
  exact run.trans (congrArg Result.ok same)

/-- Successful checked field levels lower to the CURRENT wrapping outer
body, including each actual native inner Range traversal. -/
theorem from_levels (ops : Ops) (backend : SessionABasis ops)
    (basis out : Basis) (node : U32) (n : Usize) (fuel : Nat)
    (positive : 0<n.val) (schedule : n.val*2^fuel=64)
    (h : S7Kani3BasisOuter.levels fuel basis node n=ok out) :
    verifier.accumulate_batched_with_node_loop0 ops 1#u32 node 64#usize basis n=ok out := by
  induction fuel generalizing basis node n with
  | zero =>
    have size : n.val=64 := by simpa only [pow_zero,Nat.mul_one] using schedule
    have inactive : ¬n<64#usize := by change ¬n.val<64; omega
    have same : basis=out := Result.ok.inj h
    subst out
    unfold verifier.accumulate_batched_with_node_loop0
    rw [Aeneas.Std.loop.eq_def]
    simp only [Aeneas.Std.uncurry,verifier.accumulate_batched_with_node_loop0.body,if_neg inactive]
  | succ fuel ih =>
    have powpos : 0<2^fuel := by positivity
    have small : n.val*2≤64 := by
      have np : n.val≤n.val*2^fuel := Nat.le_mul_of_pos_right _ powpos
      have sched : (n.val*2^fuel)*2=64 := by simpa only [pow_succ,Nat.mul_assoc] using schedule
      omega
    have active : n<64#usize := by change n.val<64; omega
    unfold S7Kani3BasisOuter.levels at h
    obtain ⟨basis1,hblock,h⟩ := bind_success _ _ _ h
    obtain ⟨node1,hnode,h⟩ := bind_success _ _ _ h
    have mul := checked_mul n 2#usize (by change n.val*2≤4096; omega)
    rw [mul,bind_tc_ok] at h
    have nextValue := Port3_Wrapping.wrap_mul_value n 2#usize (by change n.val*2≤4096; omega)
    have tail := ih basis1 node1 (Usize.wrapping_mul n 2#usize)
      (by rw [nextValue]; change 0<n.val*2; omega)
      (by rw [nextValue]; change n.val*2*2^fuel=64; simpa only [pow_succ,Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm] using schedule) h
    rw [S7Kani2BasisLoop.extracted_basis_block_composition _ basis node n 0#usize n.val
      (by omega) (by simp)] at hblock
    have block := Port4C_BasisInner.from_iterate ops node n
      {start:=0#usize,«end»:=n} basis basis1 n.val (by omega) rfl (by simp)
      (by rw [backend.s3_s4_mul]; exact hblock)
    unfold S7Kani3BasisOuter.t2 at hnode
    obtain ⟨square,hsquare,hnode⟩ := bind_success _ _ _ hnode
    obtain ⟨doubled,hdouble,hsub⟩ := bind_success _ _ _ hnode
    have bodyRun : verifier.accumulate_batched_with_node_loop0.body ops 1#u32 64#usize node basis n =
        ok (cont (node1,basis1,Usize.wrapping_mul n 2#usize)) := by
      unfold verifier.accumulate_batched_with_node_loop0.body
      simp only [if_pos active,block,bind_tc_ok,backend.s3_s4_mul,backend.s3_s4_double,
        backend.s3_s4_sub,hsquare,hdouble,hsub,lift]
    unfold verifier.accumulate_batched_with_node_loop0
    rw [Aeneas.Std.loop.eq_def]
    simp only [Aeneas.Std.uncurry,bodyRun]
    exact tail

#print axioms checked_mul
#print axioms from_levels
end AspisR1.Port4C_BasisOuter
end
