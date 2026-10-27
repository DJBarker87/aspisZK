from pathlib import Path
import sys
P=Path(__file__).resolve().parent;R=P.parents[1]
s='''import JFu_SelectedClaim
set_option autoImplicit false
noncomputable section
namespace AspisR1.JFu_CompositionGathers
open Aeneas Aeneas.Std Result WP FIq_Native
open pool_v1.pair_forest_semantic_terminal
'''
for k in range(4):
 closure='closure'+('' if k==0 else '_'+str(k));n=16 if k<3 else 10
 cb=f'composition_parts.{closure}.Insts.CoreOpsFunctionFnMutTupleUsizeQM31'
 s+=f'''theorem callback{k} (selected : Array field.QM31 84#usize) (i : Usize) (bound : i.val<{n}) :
    ∃ q,{cb}.call_mut selected i=ok (q,selected) := by
'''
 if k<3:
  s+=f'''  obtain ⟨q,read⟩ := JFu_SelectedClaim.source selected {k}#usize i (by change {k}<3;omega) (by omega)
  refine ⟨q,?_⟩
  unfold {cb}.call_mut
  rw [read,bind_tc_ok]
'''
 else:
  s+='''  obtain ⟨col,add,value⟩ := WP.spec_imp_exists
    (UScalar.add_spec (x:=16#usize) (y:=i) (by scalar_tac))
  have boundCol : col.val<28 := by change col.val=16+i.val at value;omega
  obtain ⟨q,read⟩ := JFu_SelectedClaim.source selected 0#usize col (by change 0<3;omega) boundCol
  refine ⟨q,?_⟩
  unfold composition_parts.closure_3.Insts.CoreOpsFunctionFnMutTupleUsizeQM31.call_mut
    POOL_V1_PAIR_FOREST_TERMINAL_C1_COLUMNS_V1
  rw [add,bind_tc_ok,read,bind_tc_ok]
'''
 s+=f'#print axioms callback{k}\n'
 s+=f'''theorem gather{k} (selected : Array field.QM31 84#usize) : ∃ out,
    array_from_fn_copy {n}#usize field.QM31.Insts.CoreMarkerCopy {cb} field.QM31.ZERO selected=ok out := by
  unfold array_from_fn_copy
  apply JFu_BoundedBuilder.source
  exact callback{k} selected
#print axioms gather{k}
'''
s+='''theorem source (selected : Array field.QM31 84#usize) : ∃ a b c m,
'''
for k in range(4):
 closure='closure'+('' if k==0 else '_'+str(k));n=16 if k<3 else 10;out=['a','b','c','m'][k]
 s+=f'    array_from_fn_copy {n}#usize field.QM31.Insts.CoreMarkerCopy composition_parts.{closure}.Insts.CoreOpsFunctionFnMutTupleUsizeQM31 field.QM31.ZERO selected=ok {out}'+(' ∧\n' if k<3 else ' := by\n')
s+='''  obtain ⟨a,ha⟩ := gather0 selected
  obtain ⟨b,hb⟩ := gather1 selected
  obtain ⟨c,hc⟩ := gather2 selected
  obtain ⟨m,hm⟩ := gather3 selected
  exact ⟨a,b,c,m,ha,hb,hc,hm⟩
#print axioms source
end AspisR1.JFu_CompositionGathers
end
'''
f=R/'lean/JFu_CompositionGathers.lean'
if '--check' in sys.argv:assert f.read_text()==s
else:f.write_text(s)
