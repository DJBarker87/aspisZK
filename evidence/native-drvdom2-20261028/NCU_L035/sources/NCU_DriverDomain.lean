import NCU_WriterPrefix
set_option autoImplicit false
noncomputable section
namespace AspisR1.NCU_DriverDomain
open Aeneas Aeneas.Std Result AspisR1CurrentCaller
open DrvC_Installation
attribute [local irreducible] verifier.candidate.prepare verifier.candidate.tx1
structure Prefix (ops : Ops) {H : Type} (D : aspis_core.digest.Digest32 H)
    (semantic : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (pub proof : Slice U8) (hash : H) where
  parsed : transport.Variant
  zero : aspis_core.field.wide_exact.WideExact
  prepared : verifier.Prepared
  scratch : Array aspis_core.field.wide_exact.WideExact 29#usize
  initial : verifier.Accumulator
  root : Array U8 32#usize
  geometry : verifier.QueryGeometry
  pending : verifier.BatchedWeights
  out : verifier.Accumulator
  after : verifier.BatchedWeights
  flushed : Slice aspis_core.field.QM31
  rootView : Slice U8
  shape : ops.op3 proof = ok (.Ok parsed)
  scan : ops.op4 proof = ok (.Ok ())
  zero_call : aspis_core.field.wide_exact.WideExact.ZERO ops = ok zero
  prepare : verifier.candidate.prepare ops D semantic proof hash none
    (Array.repeat 29#usize zero) = ok (.Ok prepared,scratch)
  root_range : core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
    proof {start:=7751#usize,«end»:=7783#usize} = ok rootView
  root_copy : core.array.TryFromArrayCopySlice.try_from 32#usize core.marker.CopyU8 rootView = ok (.Ok root)
  initial_call : ops.op20 .S2 = ok (.Ok initial)
  batch : ops.op6 D proof prepared root 0#usize hash = ok (.Ok ())
  geometry_call : ops.op19 prepared.queries 0#usize 10#usize = ok (.Ok geometry)
  pending_call : ops.op18 initial.weights.deref = ok (.Ok pending)
  query : ops.op7 proof prepared initial scratch none geometry pending 10#usize = ok (.Ok (out,after))
  flush : ops.op17 after out.weights.deref = ok flushed

/-- Every reached writer, without assuming the writer returns. -/
theorem prefix_of_reached (ops : Ops) {H : Type} (D : aspis_core.digest.Digest32 H)
    (semantic : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (pub proof : Slice U8) (split : Usize) (hash : H)
    (p : verifier.Prepared) (a : verifier.Accumulator)
    (start : compact.OFF_FOLDED_ROOT ops = ok 7751#usize)
    (finish : compact.OFF_ROUND1 ops = ok 7783#usize)
    (reached : NCU_WriterPrefix.Reached ops D semantic pub proof split hash p a) :
    split = 10#usize ∧ ∃ cut : Prefix ops D semantic pub proof hash,
      p = cut.prepared ∧ a = {cut.out with weights := ⟨cut.flushed.val,cut.flushed.property⟩} := by
  unfold NCU_WriterPrefix.Reached NCU_WriterPrefix.beforeWriter at reached
  split at reached
  · cases reached
  · rename_i splitCheck
    have same : split = 10#usize := by
      simpa only [compact.SPLIT,bne_iff_ne,not_not] using splitCheck
    cases same
    unfold NCU_PrefixTail.tail at reached
    rw [start,finish] at reached
    repeat' first
    | (solve | cases reached)
    | uncase_result
    | head_reduce reached
    | split at reached
    all_goals
      repeat' casesm (_ × _)
      simp_all only [Prod.fst,Prod.snd]
      have eq := core.result.Result.Ok.inj (Result.ok.inj reached)
      cases eq
      let cut : Prefix ops D semantic pub proof hash :=
        ⟨_,_,_,_,_,_,_,_,_,_,_,_,by assumption,by assumption,by assumption,by assumption,
          by assumption,by assumption,by assumption,by assumption,by assumption,by assumption,
          by assumption,by assumption⟩
      exact ⟨True.intro,cut,rfl,rfl⟩

#print axioms prefix_of_reached
end AspisR1.NCU_DriverDomain
end
