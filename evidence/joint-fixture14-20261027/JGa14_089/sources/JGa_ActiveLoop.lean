import JGa_ActiveMasks
import JGa_ArrayProperty
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGa_ActiveLoop
open Aeneas Aeneas.Std Result WP FIq_Native
open FIv_NativeValue (Canon)
open FIw_ArrayValue (canonical)
open pool_v1.pair_forest_copy_terminal

theorem source (n : Nat) (i : Usize) (s : Selectors) (sum : field.QM31)
    (span : i.val+n=64) (hh : canonical s.high) (hl : canonical s.low) (hs : Canon sum) :
    ∃ out,Selectors.active_literal_loop s sum i=ok out ∧ Canon out := by
  induction n generalizing i sum with
  | zero =>
    refine ⟨sum,?_,hs⟩
    rw [Selectors.active_literal_loop,if_neg (by scalar_tac : ¬(i<64#usize))]
  | succ n ih =>
    obtain ⟨mask,hm,hmem⟩ := WP.spec_imp_exists (JGa_ArrayProperty.read constants.ACTIVE_ROW_MASKS i (fun m=>m∈constants.ACTIVE_ROW_MASKS.val) (by change i.val<64;omega) (by intro m hm;exact hm))
    obtain ⟨i',hi,hiv⟩ := WP.spec_imp_exists (UScalar.add_spec (x:=i) (y:=1#usize) (by scalar_tac))
    have span' : i'.val+n=64 := by change i'.val=i.val+1 at hiv;omega
    by_cases hmask : (mask != 0#u16)=true
    · obtain ⟨q,hq,hqc⟩ := JFy_ArrayTotal.read s.high i (by change i.val<64;omega) hh
      obtain ⟨low,hlo,hlc⟩ := JGa_ActiveMasks.source s.low mask hl hmem
      obtain ⟨prod,hp,hpc,_⟩ := JFy_FieldTotal.mul q low hqc hlc
      obtain ⟨next,hn,hnc,_⟩ := FIv_PreparedTotal.add sum prod hs hpc
      obtain ⟨out,tail,hout⟩ := ih i' next span' hnc
      refine ⟨out,?_,hout⟩
      rw [Selectors.active_literal_loop,if_pos (by scalar_tac : i<64#usize),hm,bind_tc_ok,if_pos hmask,hq,bind_tc_ok,hlo,bind_tc_ok,hp,bind_tc_ok,hn,bind_tc_ok]
      change (do let i' ← i+1#usize;Selectors.active_literal_loop s next i')=ok out
      rw [hi,bind_tc_ok,tail]
    · obtain ⟨out,tail,hout⟩ := ih i' sum span' hs
      refine ⟨out,?_,hout⟩
      rw [Selectors.active_literal_loop,if_pos (by scalar_tac : i<64#usize),hm,bind_tc_ok,if_neg hmask]
      change (do let i' ← i+1#usize;Selectors.active_literal_loop s sum i')=ok out
      rw [hi,bind_tc_ok,tail]
#print axioms source

@[step] theorem full (s : Selectors) (hh : canonical s.high) (hl : canonical s.low) :
    Selectors.active s ⦃ out => Canon out ⦄ := by
  apply exists_imp_spec
  exact source 64 0#usize s field.QM31.ZERO rfl hh hl FIv_NativeValue.zero.1
#print axioms full
end AspisR1.JGa_ActiveLoop
end
