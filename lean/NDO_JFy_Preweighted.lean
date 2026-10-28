import NDO_JFy_PreweightedLoop
import RPv_FIx_WordArithmetic
set_option autoImplicit false
noncomputable section
namespace AspisR1.JFy_Preweighted
open Aeneas Aeneas.Std Result WP FIq_Native
open FIw_ArrayValue (canonical)
open pool_v1.pair_forest_semantic_terminal

@[step] theorem source {N : Usize} (packed : Array field.QM31 24#usize) (start : Usize) (a : Array field.QM31 N)
    (positive : 0<N.val) (bound : start.val+N.val≤96) (hp : canonical packed) (ha : canonical a) :
    add_preweighted packed start a ⦃ out => canonical out ⦄ := by
  obtain ⟨first,hfirst,_⟩ := UScalar.div_spec start (y:=4#usize) (by decide)
  obtain ⟨stop,hstop,vstop⟩ := WP.spec_imp_exists (UScalar.add_spec (x:=start) (y:=N) (by scalar_tac))
  have stopv : stop.val=start.val+N.val := vstop
  obtain ⟨last1,hlast1,_⟩ := WP.spec_imp_exists (UScalar.sub_spec (x:=stop) (y:=1#usize) (by scalar_tac))
  obtain ⟨last,hlast,_⟩ := UScalar.div_spec last1 (y:=4#usize) (by decide)
  have last1v := FIx_WordArithmetic.sub stop 1#usize last1 (by scalar_tac) hlast1
  have lastv := FIx_WordArithmetic.div last1 4#usize last (by decide) hlast
  have endbound : last.val<24 := by rw [lastv,last1v,stopv];change (start.val+N.val-1)/4<24;omega
  obtain ⟨out,call,hout⟩ := JFy_PreweightedLoop.source ⟨first,last,false⟩ packed start a endbound hp ha bound
  have run : add_preweighted packed start a=ok out := by
    unfold add_preweighted
    rw [hfirst,bind_tc_ok,hstop,bind_tc_ok,hlast1,bind_tc_ok,hlast,bind_tc_ok]
    exact call
  rw [run]
  exact hout
#print axioms source
end AspisR1.JFy_Preweighted
end
