import R1Z.ProverCommitEncoderGenericCollect54
import R1Z.ProverCommitEncoderMath54
/-! Generic source evaluation under explicitly stated local arithmetic laws.
Concrete native field instances are discharged in separate modules. -/
set_option autoImplicit false
namespace R1Z.ProverCommitEncoderGenericEval54
open Aeneas Aeneas.Std Result AspisR1ProducerRelease47
open ProverCommitEncoderCollect54 ProverCommitEncoderEval54

structure Arithmetic {E K : Type} [CommRing K] (inst : scalar.CodeField E)
    (valid : E → Prop) (decode : E → K) (nv : U32 → K) : Prop where
  add_success : ∀ x y, valid x → valid y → ∃ z, inst.add x y=ok z ∧ valid z ∧ decode z=decode x+decode y
  mul_success : ∀ x y, valid x → valid y → ∃ z, inst.mul x y=ok z ∧ valid z ∧ decode z=decode x*decode y
  from_success : ∀ m : U32, m.val<2147483647 → ∃ z, inst.from_m31 m=ok z ∧ valid z ∧ decode z=nv m

theorem exact_result {E K : Type} [CommRing K] (inst : scalar.CodeField E)
    (valid : E → Prop) (decode : E → K) (nv : U32 → K) (ops : Arithmetic inst valid decode nv)
    (h : Nat) (hh : h≤8) (height depth : Usize)
    (hheight : height.val=h) (hdepth : depth.val+h≤9)
    (f : Nat → E) (hf : ∀ i, i<2^h → valid (f i))
    (c : Slice E) (hc : c.val=List.ofFn (fun i : Fin (2^h) => f i.val))
    (p : Nat → U32) (hp : ∀ i, i<9 → (p i).val<2147483647) :
    ∃ z : E, generic54.eval_rec inst c depth height (nodes p)=ok (z) ∧
      valid z ∧ decode z=ProverCommitEncoderMath54.evaluate h (fun i => decode (f i)) (fun i => nv (p i)) depth.val := by
  induction h generalizing height depth f c with
  | zero =>
    have hz : height=0#usize := by scalar_tac
    refine ⟨f 0,?_,hf 0 (by simp),rfl⟩
    rw [generic54.eval_rec,hz]
    simp only [ite_true]
    rw [Slice.index_usize]
    simp [hc]
  | succ h ih =>
    have hne : height≠0#usize := by scalar_tac
    have hpow : 2^(h+1)=2*2^h := by rw [pow_succ,Nat.mul_comm]
    have hsmall : 2^h≤256 := by
      have := Nat.pow_le_pow_right (by decide : 1≤2) (show h≤8 by omega)
      exact this
    have hlen : c.val.length=2*2^h := by rw [hc,List.length_ofFn,hpow]
    let n : Usize := Usize.ofNatCore (2^h) (by have hs:=usize_bound;scalar_tac)
    have hn : n.val=2^h := rfl
    have hdiv : Slice.len c / 2#usize=ok n := by
      obtain ⟨z,hz,hval,hbv⟩ := UScalar.div_bv_spec (y:=2#usize) (Slice.len c) (by decide)
      rw [hz]
      congr 1
      apply UScalar.eq_of_val_eq
      have hlenv : (Slice.len c).val=2*2^h := hlen
      rw [hval,hlenv]
      change (2*2^h)/2=2^h
      omega
    obtain ⟨even,heven,hevenval⟩ := ProverCommitEncoderGenericCollect54.collect inst c 2#usize 0#usize 0#usize n (2^h) hn
      (by change 0+2^h<1025;omega) (by decide) (by decide)
      (by intro k hk;change 2*(0+k)+0<c.val.length;rw [hlen];omega)
      (alloc.vec.Vec.new _) (by change 0+2^h≤1024;omega)
    obtain ⟨odd,hodd,hoddval⟩ := ProverCommitEncoderGenericCollect54.collect inst c 2#usize 1#usize 0#usize n (2^h) hn
      (by change 0+2^h<1025;omega) (by decide) (by decide)
      (by intro k hk;change 2*(0+k)+1<c.val.length;rw [hlen];omega)
      (alloc.vec.Vec.new _) (by change 0+2^h≤1024;omega)
    have hevenlist : even.val=List.ofFn (fun i : Fin (2^h) => f (2*i.val)) := by
      simpa only [alloc.vec.Vec.new,List.nil_append,hc,List.getElem_ofFn,
        show (0#usize).val=0 from rfl,show (2#usize).val=2 from rfl,Nat.zero_add,Nat.add_zero] using hevenval
    have hoddlist : odd.val=List.ofFn (fun i : Fin (2^h) => f (2*i.val+1)) := by
      simpa only [alloc.vec.Vec.new,List.nil_append,hc,List.getElem_ofFn,
        show (0#usize).val=0 from rfl,show (1#usize).val=1 from rfl,
        show (2#usize).val=2 from rfl,Nat.zero_add] using hoddval
    have hinc : (Usize.wrapping_add depth 1#usize).val=depth.val+1 :=
      ProverCommitPairCounter47.next_val depth (by omega)
    have hdec : (Usize.wrapping_sub height 1#usize).val=h := by
      rw [sub_one height (by omega)];omega
    obtain ⟨a,ha,hca,hda⟩ := ih (by omega) _ _ hdec (by rw [hinc];omega)
      (fun i => f (2*i)) (by intro i hi;apply hf;rw [hpow];omega)
      (alloc.vec.Vec.deref even) hevenlist
    obtain ⟨b,hb,hcb,hdb⟩ := ih (by omega) _ _ hdec (by rw [hinc];omega)
      (fun i => f (2*i+1)) (by intro i hi;apply hf;rw [hpow];omega)
      (alloc.vec.Vec.deref odd) hoddlist
    obtain ⟨node,hnode,hcnode,hdnode⟩ := ops.from_success (p depth.val) (hp _ (by omega))
    obtain ⟨prod,hprod,hcprod,hdprod⟩ := ops.mul_success node b hcnode hcb
    obtain ⟨z,hz,hcz,hdz⟩ := ops.add_success a prod hca hcprod
    refine ⟨z,?_,hcz,?_⟩
    · rw [generic54.eval_rec]
      simp only [hne,if_false,hdiv,heven,hodd,lift,bind_tc_ok,ha,hb,nodes_index p depth (by omega)]
      rw [hnode];simp only [bind_tc_ok];rw [hprod];simp only [bind_tc_ok];exact hz
    · rw [hdz,hdprod,hda,hdb,hdnode,hinc,ProverCommitEncoderMath54.evaluate]

#print axioms exact_result
end R1Z.ProverCommitEncoderGenericEval54
