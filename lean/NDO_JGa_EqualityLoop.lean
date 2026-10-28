import NDO_JGa_EqualityCell
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGa_EqualityLoop
open Aeneas Aeneas.Std Result WP FIq_Native
open FIv_NativeValue (Canon)
open FIw_ArrayValue (canonical)
open pool_v1.pair_forest_semantic_terminal

theorem source (n : Nat) (i : Usize) (left right : Array field.QM31 10#usize) (product : field.QM31)
    (span : i.val+n=10) (hl : canonical left) (hr : canonical right) (hp : Canon product) :
    ∃ out,equality_value_loop left right product i=ok out ∧ Canon out := by
  induction n generalizing i product with
  | zero =>
    refine ⟨product,?_,hp⟩
    rw [equality_value_loop]
    simp only [lift,bind_tc_ok]
    rw [if_neg (by have len:=left.property;scalar_tac : ¬i<Slice.len (Array.to_slice left))]
  | succ n ih =>
    obtain ⟨a,ha,hac⟩ := JFy_ArrayTotal.read left i (by change i.val<10;omega) hl
    obtain ⟨b,hb,hbc⟩ := JFy_ArrayTotal.read right i (by change i.val<10;omega) hr
    obtain ⟨cell,hcell,hcc⟩ := WP.spec_imp_exists (JGa_EqualityCell.source a b hac hbc)
    unfold FIv_EqualityCell.call at hcell
    obtain ⟨next,hn,hnc,_⟩ := JFy_FieldTotal.mul product cell hp hcc
    obtain ⟨i',hi,hiv⟩ := WP.spec_imp_exists (UScalar.add_spec (x:=i) (y:=1#usize) (by scalar_tac))
    obtain ⟨out,tail,hout⟩ := ih i' next (by change i'.val=i.val+1 at hiv;omega) hnc
    refine ⟨out,?_,hout⟩
    rw [equality_value_loop]
    simp only [lift,bind_tc_ok]
    rw [if_pos (by have len:=left.property;scalar_tac : i<Slice.len (Array.to_slice left)),ha,bind_tc_ok,hb,bind_tc_ok,hcell,bind_tc_ok,hn,bind_tc_ok,hi,bind_tc_ok,tail]
#print axioms source
end AspisR1.JGa_EqualityLoop
end
