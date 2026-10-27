import JGa_LinkWeight
import JGa_CopyEndpoint
import JGa_ArrayProperty
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGa_CopyLoop
open Aeneas Aeneas.Std Result WP FIq_Native
open FIw_ArrayValue (canonical)
open pool_v1.pair_forest_copy_terminal

theorem source (n : Nat) (i : Usize) (s : Selectors) (index : U64)
    (v : PoolV1PairForestCompiledVariantV1) (patterns : Array field.QM31 14#usize)
    (pv pw cv cw : Array field.QM31 2#usize) (span : i.val+n=136)
    (hh : canonical s.high) (hl : canonical s.low) (hp : canonical patterns)
    (hpv : canonical pv) (hpw : canonical pw) (hcv : canonical cv) (hcw : canonical cw) :
    ∃ a b c d,evaluate_with_selectors_loop s index v patterns pv pw cv cw i=ok (a,b,c,d) ∧
      canonical a ∧ canonical b ∧ canonical c ∧ canonical d := by
  induction n generalizing i pv pw cv cw with
  | zero =>
    refine ⟨pv,pw,cv,cw,?_,hpv,hpw,hcv,hcw⟩
    rw [evaluate_with_selectors_loop,POOL_V1_PAIR_FOREST_COPY_TERMINAL_LINKS_V1,if_neg (by scalar_tac : ¬(i<136#usize))]
  | succ n ih =>
    obtain ⟨l,hlink,hg⟩ := WP.spec_imp_exists (JGa_ArrayProperty.read constants.COPY_LINKS i JGa_LinkBounds.Good (by change i.val<136;omega) JGa_LinkBounds.all)
    obtain ⟨weight,hw⟩ := JGa_LinkWeight.source l index v hg
    obtain ⟨⟨pv',pw'⟩,hprod,hpvc,hpwc⟩ := WP.spec_imp_exists (JGa_CopyEndpoint.source pv pw l.producer l.tag weight patterns s hpv hpw hp hh hl hg.1.1 hg.1.2.1 hg.1.2.2 hg.2.2.1)
    obtain ⟨⟨cv',cw'⟩,hcons,hcvc,hcwc⟩ := WP.spec_imp_exists (JGa_CopyEndpoint.source cv cw l.consumer l.tag weight patterns s hcv hcw hp hh hl hg.2.1.1 hg.2.1.2.1 hg.2.1.2.2 hg.2.2.1)
    obtain ⟨i',hi,hiv⟩ := WP.spec_imp_exists (UScalar.add_spec (x:=i) (y:=1#usize) (by scalar_tac))
    obtain ⟨a,b,c,d,tail,ha,hb,hc,hd⟩ := ih i' pv' pw' cv' cw' (by change i'.val=i.val+1 at hiv;omega) hpvc hpwc hcvc hcwc
    refine ⟨a,b,c,d,?_,ha,hb,hc,hd⟩
    rw [evaluate_with_selectors_loop,POOL_V1_PAIR_FOREST_COPY_TERMINAL_LINKS_V1,if_pos (by scalar_tac : i<136#usize),hlink,bind_tc_ok,hw,bind_tc_ok,hprod,bind_tc_ok]
    change (do let (cv',cw') ← accumulate_endpoint cv cw l.consumer l.tag weight patterns s;let i' ← i+1#usize;evaluate_with_selectors_loop s index v patterns pv' pw' cv' cw' i')=ok (a,b,c,d)
    rw [hcons,bind_tc_ok]
    change (do let i' ← i+1#usize;evaluate_with_selectors_loop s index v patterns pv' pw' cv' cw' i')=ok (a,b,c,d)
    rw [hi,bind_tc_ok,tail]
#print axioms source
end AspisR1.JGa_CopyLoop
end
