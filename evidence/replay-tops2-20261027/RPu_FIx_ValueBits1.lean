import RPu_FIx_ValueBitModel
import RPu_FIq_Native09
import RPu_FIx_ValueIndices
import RPu_FIv_SubMap
set_option autoImplicit false
noncomputable section
namespace AspisR1.FIx_ValueBits1
open Aeneas Aeneas.Std Result FIq_Native
open FIv_NativeArithmetic (NQ)
open FIv_NativeValue (K Canon decode)
open FIw_ArrayValue (canonical decoded)
abbrev Openings := state_only_poseidon.StateOnlyPoseidonOpenings
abbrev loop := pool_v1.pair_forest_semantic_terminal.add_value_lanes_loop1

theorem value (n : Nat) (index : Usize) (o returned : Openings)
    (range out : Array NQ 33#usize) (span : index.val+n=10)
    (ho : canonical o.succ_z) (hp : canonical range)
    (success : loop o range index=ok (returned,out)) :
    returned=o ∧ canonical out ∧ decoded out=FIx_ValueBitModel.model o.succ_z 10 n index.val (decoded range) := by
  induction n generalizing index range with
  | zero =>
    rw [loop,pool_v1.pair_forest_semantic_terminal.add_value_lanes_loop1] at success
    have stop : ¬index<10#usize := by scalar_tac
    rw [if_neg stop] at success
    obtain ⟨rfl,rfl⟩ := Prod.mk.inj (Result.ok.inj success)
    exact ⟨rfl,hp,rfl⟩
  | succ n ih =>
    rw [loop,pool_v1.pair_forest_semantic_terminal.add_value_lanes_loop1] at success
    have more : index<10#usize := by scalar_tac
    rw [if_pos more] at success
    obtain ⟨q,hq,success⟩ := FIv_Map.bind_success _ _ _ success
    obtain ⟨square,hsquare,success⟩ := FIv_Map.bind_success _ _ _ success
    obtain ⟨residual,hresidual,success⟩ := FIv_Map.bind_success _ _ _ success
    obtain ⟨slot,hslot,success⟩ := FIv_Map.bind_success _ _ _ success
    obtain ⟨updated,hupdated,success⟩ := FIv_Map.bind_success _ _ _ success
    obtain ⟨next,hnext,success⟩ := FIv_Map.bind_success _ _ _ success
    have hqcan := FIv_NativeArray.canonical o.succ_z index q ho hq
    have vsquare := FIx_SquareValue.value q square hqcan hsquare
    have vresidual := FIv_SubMap.qm square q residual vsquare.1 hqcan hresidual
    have vi := FIx_ValueIndices.inc index next hnext
    have vslot := FIx_ValueIndices.offset 10#usize index slot hslot
    have hb := FIx_ValueIndices.bound 10#usize index slot (by decide) (by omega) vslot
    have vu := FIw_ArrayValue.update range updated slot residual (hb) hp vresidual.1 hupdated
    have rest := ih next updated (by omega) vu.1 success
    refine ⟨rest.1,rest.2.1,?_⟩
    change decoded out=FIx_ValueBitModel.model o.succ_z 10 n (index.val+1) (FIx_ValueBitModel.step o.succ_z 10 index.val (decoded range))
    rw [rest.2.2,vu.2,vresidual.2,vsquare.2,←FIv_NativeArray.read o.succ_z index q hq,vi]
    congr 1
    funext j
    simp only [FIx_ValueBitModel.step,FIx_ValueBitModel.bit,Function.update_apply,Fin.ext_iff,vslot]
    rfl
#print axioms value
end AspisR1.FIx_ValueBits1
end
