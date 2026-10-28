import RPu_FIq_Native14
import RPv_JFy_ArrayTotal
import RPv_FIv_PreparedNewTotal
import ExtractedMaskReverseRange
set_option autoImplicit false
noncomputable section
namespace AspisR1.JFy_SelectorInner
open Aeneas Aeneas.Std Result WP FIq_Native
open FIv_NativeArithmetic (NQ qm)
open FIv_NativeValue (Canon)
open FIv_PreparedNew (NP prepared)
open ExtractedMaskReverseRange
open pool_v1.pair_forest_copy_terminal

theorem source {N : Usize} (n : Nat) (iter : ReverseRange) (weights : Array NQ N)
    (p : NP) (x : NQ) (hx : Canon x)
    (hp : ExtractedMaskPreparedState.PreparedFor (prepared p) (qm x))
    (start : iter.iter.start.val=0) (stop : iter.iter.end.val=n)
    (bound : 2*n≤N.val) (hc : FIw_ArrayValue.canonical weights) :
    ∃ out,Selectors.expand_loop0_loop0 iter weights p=ok out ∧ FIw_ArrayValue.canonical out := by
  induction n generalizing iter weights with
  | zero =>
    refine ⟨weights,?_,hc⟩
    rw [Selectors.expand_loop0_loop0]
    rw [reverse_next_done iter (by omega),bind_tc_ok]
    rfl
  | succ n ih =>
    let i := Usize.wrapping_sub iter.iter.end 1#usize
    have iv : i.val=n := by
      dsimp only [i]
      rw [wrapping_sub_one_val _ (by omega),stop]
      omega
    obtain ⟨parent,read,hparent⟩ := JFy_ArrayTotal.read weights i (by omega) hc
    obtain ⟨right,mul,hright,_⟩ := FIv_PreparedTotal.mul p x parent hx hparent hp
    obtain ⟨left,sub,hleft,_⟩ := JFy_FieldTotal.sub parent right hparent hright
    obtain ⟨j,twice,jv⟩ := WP.spec_imp_exists (UScalar.mul_spec (x:=2#usize) (y:=i) (by scalar_tac))
    have jval : j.val=2*n := by change j.val=2*i.val at jv;omega
    obtain ⟨w1,update1,hw1⟩ := JFy_ArrayTotal.update weights j left (by omega) hc hleft
    obtain ⟨k,add,kv⟩ := WP.spec_imp_exists (UScalar.add_spec (x:=j) (y:=1#usize) (by scalar_tac))
    have kval : k.val=2*n+1 := by change k.val=j.val+1 at kv;omega
    obtain ⟨w2,update2,hw2⟩ := JFy_ArrayTotal.update w1 k right (by omega) hw1 hright
    let next : ReverseRange := ⟨{iter.iter with «end»:=i}⟩
    obtain ⟨out,tail,hout⟩ := ih next w2 (by exact start) iv (by omega) hw2
    refine ⟨out,?_,hout⟩
    rw [Selectors.expand_loop0_loop0]
    rw [reverse_next_step iter (by omega),bind_tc_ok]
    change (do let a ← Array.index_usize weights i
               let b ← field.PreparedQm31Multiplier.mul p a
               let c ← field.QM31.sub a b
               let j ← 2#usize*i
               let w1 ← Array.update weights j c
               let k ← j+1#usize
               let w2 ← Array.update w1 k b
               Selectors.expand_loop0_loop0 next w2 p)=ok out
    rw [read,bind_tc_ok,mul,bind_tc_ok,sub,bind_tc_ok,twice,bind_tc_ok,update1,bind_tc_ok,add,bind_tc_ok,update2,bind_tc_ok,tail]
#print axioms source
end AspisR1.JFy_SelectorInner
end
