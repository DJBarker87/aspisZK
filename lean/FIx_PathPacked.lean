import FIx_PathMeaning
import FIx_PreweightedMeaning
import FIx_HighSum
set_option autoImplicit false
noncomputable section
namespace AspisR1.FIx_PathPacked
open Aeneas Aeneas.Std Result FIq_Native
open FIv_NativeArithmetic (NQ)
open FIv_NativeValue (K Canon decode)
open FIw_ArrayValue (canonical decoded)
abbrev Openings := state_only_poseidon.StateOnlyPoseidonOpenings
abbrev Selectors := pool_v1.pair_forest_copy_terminal.Selectors

def ranges : Slice (core.ops.range.Range Usize) := Array.to_slice (Array.make 1#usize [⟨57#usize,63#usize⟩])
def selector (s : Selectors) : K := FIx_HighSumOuter.ranges ranges.val s 0*
  (((FIv_NativeArray.value s.low 1+FIv_NativeArray.value s.low 5)+FIv_NativeArray.value s.low 9)+FIv_NativeArray.value s.low 13)

theorem range_bounds : ∀ r∈ranges.val,r.start.val≤r.end.val ∧ r.end.val≤64 := by
  intro r hr
  simp only [ranges,Array.to_slice,Array.make,List.mem_cons,List.not_mem_nil,or_false] at hr
  subst r
  constructor <;> scalar_tac

theorem value (packed out : Array NQ 24#usize) (o : Openings) (selectors : Selectors)
    (hp : canonical packed) (hz : canonical o.z) (hs : canonical o.succ_z)
    (hh : canonical selectors.high) (hl : canonical selectors.low)
    (success : pool_v1.pair_forest_semantic_terminal.add_path_lanes packed o selectors=ok out) :
    canonical out ∧ ∀ j : Fin (24#usize).val,
      decoded out j=decoded packed j+FIx_SelectedMeaning.contribution
        (FIx_PathMeaning.coefficients (selector selectors) (FIv_NativeArray.value o.z 0)
          (FIv_NativeArray.value o.z) (FIv_NativeArray.value o.succ_z)) 32 j.val := by
  unfold pool_v1.pair_forest_semantic_terminal.add_path_lanes at success
  obtain ⟨s,hslice,success⟩ := FIv_Map.bind_success _ _ _ success
  have same : s=ranges := (Result.ok.inj hslice).symm
  subst s
  obtain ⟨q,hq,success⟩ := FIv_Map.bind_success _ _ _ success
  obtain ⟨q1,hq1,success⟩ := FIv_Map.bind_success _ _ _ success
  obtain ⟨q2,hq2,success⟩ := FIv_Map.bind_success _ _ _ success
  obtain ⟨q3,hq3,success⟩ := FIv_Map.bind_success _ _ _ success
  obtain ⟨q4,hq4,success⟩ := FIv_Map.bind_success _ _ _ success
  obtain ⟨q5,hq5,success⟩ := FIv_Map.bind_success _ _ _ success
  obtain ⟨q6,hq6,success⟩ := FIv_Map.bind_success _ _ _ success
  obtain ⟨q7,hq7,success⟩ := FIv_Map.bind_success _ _ _ success
  obtain ⟨pathSelector,hselector,success⟩ := FIv_Map.bind_success _ _ _ success
  obtain ⟨path,hpath,success⟩ := FIv_Map.bind_success _ _ _ success
  have vq := FIx_HighSum.value selectors ranges q range_bounds hh hq
  have c1 := FIv_NativeArray.canonical selectors.low 1#usize q1 hl hq1
  have c2 := FIv_NativeArray.canonical selectors.low 5#usize q2 hl hq2
  have v3 := FIv_NativeValue.add q1 q2 q3 c1 c2 hq3
  have c4 := FIv_NativeArray.canonical selectors.low 9#usize q4 hl hq4
  have v5 := FIv_NativeValue.add q3 q4 q5 v3.1 c4 hq5
  have c6 := FIv_NativeArray.canonical selectors.low 13#usize q6 hl hq6
  have v7 := FIv_NativeValue.add q5 q6 q7 v5.1 c6 hq7
  have vsel := FIv_NativeValue.mul q q7 pathSelector vq.1 v7.1 hselector
  have selValue : decode pathSelector=selector selectors := by
    rw [vsel.2,vq.2,v7.2,v5.2,v3.2,←FIv_NativeArray.read selectors.low 1#usize q1 hq1,
      ←FIv_NativeArray.read selectors.low 5#usize q2 hq2,←FIv_NativeArray.read selectors.low 9#usize q4 hq4,
      ←FIv_NativeArray.read selectors.low 13#usize q6 hq6]
    rfl
  have vp := FIx_PathMeaning.value pathSelector o path vsel.1 hz hs hpath
  have packedValue := FIx_PreweightedMeaning.value packed out 32#usize path
    (FIx_PathMeaning.coefficients (decode pathSelector) (FIv_NativeArray.value o.z 0)
      (FIv_NativeArray.value o.z) (FIv_NativeArray.value o.succ_z)) vp.2 (by decide) (by decide) hp vp.1 success
  refine ⟨packedValue.1,?_⟩
  intro j
  rw [packedValue.2 j,selValue]
  rfl
#print axioms range_bounds
#print axioms value
end AspisR1.FIx_PathPacked
end
