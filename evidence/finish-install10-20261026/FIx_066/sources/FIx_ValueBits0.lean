import FIx_ValueBitModel
import FIx_ValueIndices
import FIv_SubMap
set_option autoImplicit false
noncomputable section
namespace AspisR1.FIx_ValueBits0
open Aeneas Aeneas.Std Result FIq_Native
open FIv_NativeArithmetic (NQ)
open FIv_NativeValue (K Canon decode)
open FIw_ArrayValue (canonical decoded)
abbrev Openings := state_only_poseidon.StateOnlyPoseidonOpenings
abbrev loop := pool_v1.pair_forest_semantic_terminal.add_value_lanes_loop0

theorem value (n : Nat) (index : Usize) (o returned : Openings)
    (range out : Array NQ 33#usize) (span : index.val+n=10)
    (ho : canonical o.z) (hp : canonical range)
    (success : loop o range index=ok (returned,out)) :
    returned=o ∧ canonical out ∧ decoded out=FIx_ValueBitModel.model o.z 0 n index.val (decoded range) := by
  induction n generalizing index range with
  | zero =>
    rw [loop,pool_v1.pair_forest_semantic_terminal.add_value_lanes_loop0] at success
    have stop : ¬index<10#usize := by scalar_tac
    rw [if_neg stop] at success
    obtain ⟨rfl,rfl⟩ := Prod.mk.inj (Result.ok.inj success)
    exact ⟨rfl,hp,rfl⟩
  | succ n ih =>
    rw [loop,pool_v1.pair_forest_semantic_terminal.add_value_lanes_loop0] at success
    have more : index<10#usize := by scalar_tac
    rw [if_pos more] at success
    obtain ⟨q,hq,success⟩ := FIv_Map.bind_success _ _ _ success
    obtain ⟨square,hsquare,success⟩ := FIv_Map.bind_success _ _ _ success
    obtain ⟨residual,hresidual,success⟩ := FIv_Map.bind_success _ _ _ success
    obtain ⟨updated,hupdated,success⟩ := FIv_Map.bind_success _ _ _ success
    obtain ⟨next,hnext,success⟩ := FIv_Map.bind_success _ _ _ success
    have hqcan := FIv_NativeArray.canonical o.z index q ho hq
    have vsquare := FIx_SquareValue.value q square hqcan hsquare
    have vresidual := FIv_SubMap.qm square q residual vsquare.1 hqcan hresidual
    have vi := FIx_ValueIndices.inc index next hnext
    have vu := FIw_ArrayValue.update range updated index residual (by change index.val<33;omega) hp vresidual.1 hupdated
    have rest := ih next updated (by omega) vu.1 success
    refine ⟨rest.1,rest.2.1,?_⟩
    rw [rest.2.2,vu.2,vresidual.2,vsquare.2,←FIv_NativeArray.read o.z index q hq,vi]
    congr 1
    funext j
    simp only [FIx_ValueBitModel.step,FIx_ValueBitModel.bit,Function.update_apply,Fin.ext_iff,Nat.zero_add]
#print axioms value
end AspisR1.FIx_ValueBits0
end
