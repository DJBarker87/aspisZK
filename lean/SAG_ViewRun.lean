import SAG_CommonTail
import SAG_ViewTail
set_option autoImplicit false
noncomputable section
namespace AspisR1.SAG_ViewRun
open Aeneas Aeneas.Std Result VTop_Stages

/-- All message ranges and the finish return belong to the SAME successful
TX2 invocation, not to a separately selected successful finish. -/
theorem reached (ops : Ops) {Hash : Type}
    (D : aspis_core.digest.Digest32 Hash) (hash : Hash)
    (pub proof checkpoint : Slice U8) (obs : Option (verifier.Phase → Result Unit))
    (accepted : verifier.candidate.tx2_common ops D pub proof checkpoint hash obs = ok (.Ok ())) :
    ∃ (p : verifier.Prepared) (saved : verifier.Accumulator)
      (g : Array aspis_core.field.wide_exact.WideExact 29#usize)
      (geometry : verifier.QueryGeometry) (pending : verifier.BatchedWeights)
      (returned : verifier.Accumulator) (after : verifier.BatchedWeights)
      (inactive : aspis_core.field.wide_exact.WideExact) (round0 folded round1 finalStart queryStart : Usize)
      (r0 r1 fm : Slice U8) (flushed : Slice aspis_core.field.QM31)
      (back : Slice aspis_core.field.QM31 → alloc.vec.Vec aspis_core.field.QM31),
      ops.op18 D checkpoint proof pub .S2 hash = ok (.Ok (p,saved)) ∧
      ops.op6 proof p saved g obs geometry pending 22#usize = ok (.Ok (returned,after)) ∧
      ops.op22 = ok round0 ∧ ops.op15 = ok folded ∧ ops.op14 = ok round1 ∧
      alloc.vec.Vec.deref_mut returned.weights = (returned.weights.deref,back) ∧
      ops.op9 after returned.weights.deref = ok flushed ∧
      ops.op21 = ok finalStart ∧ ops.op20 = ok queryStart ∧
      core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
        proof {start := round0, «end» := folded} = ok r0 ∧
      core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
        proof {start := round1, «end» := finalStart} = ok r1 ∧
      core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
        proof {start := finalStart, «end» := queryStart} = ok fm ∧
      ops.op19 (SAG_ViewTail.view inactive r0 r1 fm) p {returned with weights := back flushed} obs = ok (.Ok ()) := by
  obtain ⟨p,saved,g,geometry,pending,returned,after,inactive,r0at,folded,r1at,
    reader,query,h0,hf,h1,tail⟩ := SAG_CommonTail.reached ops D hash pub proof checkpoint obs accepted
  obtain ⟨flushed,back,r0,r1,fm,last,queries,deref,flush,hl,hq,read0,read1,readf,finish⟩ :=
    SAG_ViewTail.reached ops proof p obs inactive r0at folded r1at (returned,after) tail
  exact ⟨p,saved,g,geometry,pending,returned,after,inactive,r0at,folded,r1at,last,queries,
    r0,r1,fm,flushed,back,reader,query,h0,hf,h1,deref,flush,hl,hq,read0,read1,readf,finish⟩

#print axioms reached
end AspisR1.SAG_ViewRun
end
