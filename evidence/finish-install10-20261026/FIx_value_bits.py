from pathlib import Path
P=Path(__file__).resolve().parents[2]
for k,(field,offset) in enumerate([('z',0),('succ_z',10),('xor12_z',20)]):
 mod=f'FIx_ValueBits{k}'
 h=f'''import FIx_ValueBitModel
import FIq_Native09
import FIx_ValueIndices
import FIv_SubMap
set_option autoImplicit false
noncomputable section
namespace AspisR1.{mod}
open Aeneas Aeneas.Std Result FIq_Native
open FIv_NativeArithmetic (NQ)
open FIv_NativeValue (K Canon decode)
open FIw_ArrayValue (canonical decoded)
abbrev Openings := state_only_poseidon.StateOnlyPoseidonOpenings
abbrev loop := pool_v1.pair_forest_semantic_terminal.add_value_lanes_loop{k}

theorem value (n : Nat) (index : Usize) (o returned : Openings)
    (range out : Array NQ 33#usize) (span : index.val+n=10)
    (ho : canonical o.{field}) (hp : canonical range)
    (success : loop o range index=ok (returned,out)) :
    returned=o ∧ canonical out ∧ decoded out=FIx_ValueBitModel.model o.{field} {offset} n index.val (decoded range) := by
  induction n generalizing index range with
  | zero =>
    rw [loop,pool_v1.pair_forest_semantic_terminal.add_value_lanes_loop{k}] at success
    have stop : ¬index<10#usize := by scalar_tac
    rw [if_neg stop] at success
    obtain ⟨rfl,rfl⟩ := Prod.mk.inj (Result.ok.inj success)
    exact ⟨rfl,hp,rfl⟩
  | succ n ih =>
    rw [loop,pool_v1.pair_forest_semantic_terminal.add_value_lanes_loop{k}] at success
    have more : index<10#usize := by scalar_tac
    rw [if_pos more] at success
    obtain ⟨q,hq,success⟩ := FIv_Map.bind_success _ _ _ success
    obtain ⟨square,hsquare,success⟩ := FIv_Map.bind_success _ _ _ success
    obtain ⟨residual,hresidual,success⟩ := FIv_Map.bind_success _ _ _ success
'''
 if k:
  h+='    obtain ⟨slot,hslot,success⟩ := FIv_Map.bind_success _ _ _ success\n'
 h+='''    obtain ⟨updated,hupdated,success⟩ := FIv_Map.bind_success _ _ _ success
    obtain ⟨next,hnext,success⟩ := FIv_Map.bind_success _ _ _ success
'''
 h+=f'    have hqcan := FIv_NativeArray.canonical o.{field} index q ho hq\n'
 h+='''    have vsquare := FIx_SquareValue.value q square hqcan hsquare
    have vresidual := FIv_SubMap.qm square q residual vsquare.1 hqcan hresidual
    have vi := FIx_ValueIndices.inc index next hnext
'''
 if k:
  h+=f'    have vslot := FIx_ValueIndices.offset {offset}#usize index slot hslot\n'
  h+=f'    have hb := FIx_ValueIndices.bound {offset}#usize index slot (by decide) (by omega) vslot\n'
  slot='slot';bound='hb'
 else:
  slot='index';bound='by change index.val<33;omega'
 h+=f'    have vu := FIw_ArrayValue.update range updated {slot} residual ({bound}) hp vresidual.1 hupdated\n'
 h+='''    have rest := ih next updated (by omega) vu.1 success
    refine ⟨rest.1,rest.2.1,?_⟩
'''
 h+=f'    change decoded out=FIx_ValueBitModel.model o.{field} {offset} n (index.val+1) (FIx_ValueBitModel.step o.{field} {offset} index.val (decoded range))\n'
 h+=f'    rw [rest.2.2,vu.2,vresidual.2,vsquare.2,←FIv_NativeArray.read o.{field} index q hq,vi]\n'
 h+='    congr 1\n    funext j\n'
 h+=f'    simp only [FIx_ValueBitModel.step,FIx_ValueBitModel.bit,Function.update_apply,Fin.ext_iff'+(',vslot' if k else ',Nat.zero_add')+']\n'
 if k:h+='    rfl\n'
 h+=f'#print axioms value\nend AspisR1.{mod}\nend\n'
 (P/f'lean/{mod}.lean').write_text(h)
