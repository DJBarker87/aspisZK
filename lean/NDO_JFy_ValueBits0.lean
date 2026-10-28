import RPv_JFy_ArrayTotal
import RPv_JFy_SquareTotal
import RPu_FIq_Native09
set_option autoImplicit false
noncomputable section
namespace AspisR1.JFy_ValueBits0
open Aeneas Aeneas.Std Result WP FIq_Native
open FIw_ArrayValue (canonical)
open pool_v1.pair_forest_semantic_terminal

theorem source (n : Nat) (i : Usize) (o : state_only_poseidon.StateOnlyPoseidonOpenings)
    (range : Array field.QM31 33#usize) (span : i.val+n=10)
    (ho : canonical o.z) (hr : canonical range) :
    ∃ out,add_value_lanes_loop0 o range i=ok (o,out) ∧ canonical out := by
  induction n generalizing i range with
  | zero =>
    refine ⟨range,?_,hr⟩
    rw [add_value_lanes_loop0]
    rw [if_neg (by scalar_tac : ¬(i<10#usize))]
  | succ n ih =>
    have running : i<10#usize := by scalar_tac
    obtain ⟨q,hq,hqc⟩ := JFy_ArrayTotal.read o.z i (by change i.val<16;omega) ho
    obtain ⟨sq,hs,hsc,_⟩ := JFy_SquareTotal.source q hqc
    obtain ⟨bit,hb,hbc,_⟩ := JFy_FieldTotal.sub sq q hsc hqc
    obtain ⟨r1,hu,hr1⟩ := JFy_ArrayTotal.update range i bit (by change i.val<33;omega) hr hbc
    obtain ⟨i1,hi1,iv⟩ := WP.spec_imp_exists (UScalar.add_spec (x:=i) (y:=1#usize) (by scalar_tac))
    have ival : i1.val=i.val+1 := iv
    obtain ⟨out,tail,hout⟩ := ih i1 r1 (by omega) hr1
    refine ⟨out,?_,hout⟩
    rw [add_value_lanes_loop0,if_pos running,hq,bind_tc_ok,hs,bind_tc_ok,hb,bind_tc_ok,hu,bind_tc_ok,hi1,bind_tc_ok,tail]
#print axioms source
end AspisR1.JFy_ValueBits0
end
