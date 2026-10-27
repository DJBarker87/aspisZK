import FJh_ProjectedAfter
import FIq_Native03
import FJa_PoseidonOrigins
import FJb_PairProjection
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJh_ProjectedCall
open Aeneas Aeneas.Std Result FIq_Native
open FIv_NativeArithmetic (NQ)
open FIv_PreparedNew (NP)
open FJa_PoseidonOrigins (Openings)
open FJh_ProjectedAfter (Packed)
abbrev State := Array NQ 16#usize
abbrev Capture := state_only_poseidon.evaluate_state_only_poseidon_oracle_projected.closure_2
abbrev call := state_only_poseidon.evaluate_state_only_poseidon_oracle_projected.closure_2.Insts.CoreOpsFunctionFnMutTupleUsizeQM31.call_mut
def slice (a : State) (start stop : Usize) :=
  core.array.Array.index (core.ops.index.IndexSlice
    (core.slice.index.SliceIndexRangeUsizeSlice NQ)) a ⟨start,stop⟩
/-- Symbolic unfolding of the installed output callback,without evaluating
any recurrence,pack or channel-sum body. -/
theorem factor (o : Openings) (internal : State) (block : NP) (p : Array NP 3#usize)
    (l f : Packed) (g : Usize) :
    call (o,internal,block,p,l,f) g=(do
      let start ← 4#usize*g
      let stop ← start+4#usize
      let ts ← slice o.succ_z start stop
      let target ← field.qm31_pack_base4 ts
      let ins ← slice internal start stop
      let ip ← field.qm31_pack_base4 ins
      let out ← FJh_ProjectedAfter.source target ip l f p block g
      ok (out,(o,internal,block,p,l,f))) := by
  simp only [call,
    state_only_poseidon.evaluate_state_only_poseidon_oracle_projected.closure_2.Insts.CoreOpsFunctionFnMutTupleUsizeQM31.call_mut,
    FJh_ProjectedAfter.source,slice,bind_assoc_eq]
/-- Reached exact operands and return capture from the SAME installed call. -/
theorem reached (o : Openings) (internal : State) (block : NP) (p : Array NP 3#usize)
    (l f : Packed) (g : Usize) (out : NQ) (last : Capture)
    (run : call (o,internal,block,p,l,f) g=ok (out,last)) :
    ∃ (start stop : Usize) (ts ins : Slice NQ) (target ip : NQ),
      (4#usize*g : Result Usize)=ok start ∧ (start+4#usize : Result Usize)=ok stop ∧
      slice o.succ_z start stop=ok ts ∧ field.qm31_pack_base4 ts=ok target ∧
      slice internal start stop=ok ins ∧ field.qm31_pack_base4 ins=ok ip ∧
      FJh_ProjectedAfter.source target ip l f p block g=ok out ∧
      last=(o,internal,block,p,l,f) := by
  rw [factor] at run
  obtain ⟨start,hstart,run⟩ := FIv_Map.bind_success _ _ _ run
  obtain ⟨stop,hstop,run⟩ := FIv_Map.bind_success _ _ _ run
  obtain ⟨ts,hts,run⟩ := FIv_Map.bind_success _ _ _ run
  obtain ⟨target,htarget,run⟩ := FIv_Map.bind_success _ _ _ run
  obtain ⟨ins,hins,run⟩ := FIv_Map.bind_success _ _ _ run
  obtain ⟨ip,hip,run⟩ := FIv_Map.bind_success _ _ _ run
  obtain ⟨v,hv,run⟩ := FIv_Map.bind_success _ _ _ run
  obtain ⟨rfl,rfl⟩ := Prod.mk.inj (Result.ok.inj run)
  exact ⟨start,stop,ts,ins,target,ip,hstart,hstop,hts,htarget,hins,hip,hv,rfl⟩
#print axioms factor
#print axioms reached
end AspisR1.FJh_ProjectedCall
end
