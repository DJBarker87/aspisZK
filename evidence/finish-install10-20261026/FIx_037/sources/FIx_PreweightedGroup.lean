import FIx_PreweightedPack
set_option autoImplicit false
noncomputable section
namespace AspisR1.FIx_PreweightedGroup
open Aeneas Aeneas.Std Result FIq_Native
open FIv_NativeArithmetic (NQ)
open FIv_NativeValue (K Canon decode)
open FIw_ArrayValue (canonical decoded)

def run {N : Usize} (packed : Array NQ 24#usize) (group start : Usize) (values : Array NQ N) :
    Result (Array NQ 24#usize) := do
  let lanes ← array_from_fn_copy 4#usize field.QM31.Insts.CoreMarkerCopy
    (pool_v1.pair_forest_semantic_terminal.add_preweighted.closure.Insts.CoreOpsFunctionFnMutTupleUsizeQM31 N)
    field.QM31.ZERO (group,start,values)
  let q ← Array.index_usize packed group
  let s ← lift (Array.to_slice lanes)
  let q1 ← field.qm31_pack_base4 s
  let q2 ← field.QM31.add q q1
  Array.update packed group q2

def increment {N : Usize} (values : Array NQ N) (start group : Nat) : K :=
  FIx_PreweightedPack.pack (fun i=>FIx_PreweightedSelect.selected values start group i.val)

def step {N : Usize} (values : Array NQ N) (start group : Nat) (old : Fin (24#usize).val → K) :
    Fin (24#usize).val → K := fun j=>if j.val=group then old j+increment values start group else old j

theorem value {N : Usize} (packed out : Array NQ 24#usize) (group start : Usize) (values : Array NQ N)
    (hg : group.val<(24#usize).val) (hp : canonical packed) (hv : canonical values)
    (called : run packed group start values=ok out) :
    canonical out ∧ decoded out=step values start.val group.val (decoded packed) := by
  unfold run at called
  obtain ⟨lanes,hlanes,called⟩ := FIv_Map.bind_success _ _ _ called
  obtain ⟨q,hq,called⟩ := FIv_Map.bind_success _ _ _ called
  obtain ⟨slice,hslice,called⟩ := FIv_Map.bind_success _ _ _ called
  have hs : slice=Array.to_slice lanes := (Result.ok.inj hslice).symm
  subst slice
  obtain ⟨q1,hq1,called⟩ := FIv_Map.bind_success _ _ _ called
  obtain ⟨q2,hq2,called⟩ := FIv_Map.bind_success _ _ _ called
  have vpack := FIx_PreweightedPack.value values start group lanes q1 hv hlanes hq1
  have hcanonical := FIv_NativeArray.canonical packed group q hp hq
  have vsum := FIv_NativeValue.add q q1 q2 hcanonical vpack.1 hq2
  have vout := FIw_ArrayValue.update packed out group q2 hg hp vsum.1 called
  refine ⟨vout.1,?_⟩
  rw [vout.2,vsum.2,vpack.2,FIw_ArrayReadValue.read packed group hg q hq]
  funext j
  unfold step increment
  by_cases same : j=⟨group.val,hg⟩
  · subst j
    rw [Function.update_self,if_pos rfl]
  · rw [Function.update_of_ne same,if_neg (fun h=>same (Fin.ext h))]

#print axioms value
end AspisR1.FIx_PreweightedGroup
end
