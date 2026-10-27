from pathlib import Path
R=Path(__file__).resolve().parents[2]
for k,field in enumerate(['z','succ_z','xor12_z']):
 mod=f'JFy_ValueBits{k}';fn=f'add_value_lanes_loop{k}';off=10*k
 imp='JFy_ArrayTotal' if k==0 else f'JFy_ValueBits{k-1}'
 s=f'''import {imp}
import JFy_SquareTotal
import FIq_Native09
set_option autoImplicit false
noncomputable section
namespace AspisR1.{mod}
open Aeneas Aeneas.Std Result WP FIq_Native
open FIw_ArrayValue (canonical)
open pool_v1.pair_forest_semantic_terminal

theorem source (n : Nat) (i : Usize) (o : state_only_poseidon.StateOnlyPoseidonOpenings)
    (range : Array field.QM31 33#usize) (span : i.val+n=10)
    (ho : canonical o.{field}) (hr : canonical range) :
    ∃ out,{fn} o range i=ok (o,out) ∧ canonical out := by
  induction n generalizing i range with
  | zero =>
    refine ⟨range,?_,hr⟩
    rw [{fn}]
    rw [if_neg (by scalar_tac : ¬(i<10#usize))]
  | succ n ih =>
    have running : i<10#usize := by scalar_tac
    obtain ⟨q,hq,hqc⟩ := JFy_ArrayTotal.read o.{field} i (by change i.val<16;omega) ho
    obtain ⟨sq,hs,hsc,_⟩ := JFy_SquareTotal.source q hqc
    obtain ⟨bit,hb,hbc,_⟩ := JFy_FieldTotal.sub sq q hsc hqc
'''
 if k==0:
  s+='    obtain ⟨r1,hu,hr1⟩ := JFy_ArrayTotal.update range i bit (by change i.val<33;omega) hr hbc\n'
 else:
  s+=f'''    obtain ⟨j,hj,jv⟩ := WP.spec_imp_exists (UScalar.add_spec (x:={off}#usize) (y:=i) (by scalar_tac))
    have jval : j.val={off}+i.val := jv
    obtain ⟨r1,hu,hr1⟩ := JFy_ArrayTotal.update range j bit (by change j.val<33;omega) hr hbc
'''
 s+='''    obtain ⟨i1,hi1,iv⟩ := WP.spec_imp_exists (UScalar.add_spec (x:=i) (y:=1#usize) (by scalar_tac))
    have ival : i1.val=i.val+1 := iv
    obtain ⟨out,tail,hout⟩ := ih i1 r1 (by omega) hr1
    refine ⟨out,?_,hout⟩
'''
 s+=f'    rw [{fn},if_pos running,hq,bind_tc_ok,hs,bind_tc_ok,hb,bind_tc_ok'
 if k:s+=',hj,bind_tc_ok'
 s+=',hu,bind_tc_ok,hi1,bind_tc_ok,tail]\n'
 s+=f'#print axioms source\nend AspisR1.{mod}\nend\n'
 (R/'lean'/f'{mod}.lean').write_text(s)
