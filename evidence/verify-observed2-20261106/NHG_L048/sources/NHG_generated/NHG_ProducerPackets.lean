import NHG_FrontierPackets
import NHG_StdBytes
set_option autoImplicit false
open Aeneas Aeneas.Std Result AspisR1PublicPreparation
namespace AspisR1.NHG_ProducerPackets
open SerializerFields AspisR1PublicSerializer.Whole431
abbrev Frontier := Array (Array U32 8#usize) 20#usize
abbrev Outcome := Result (core.result.Result ByteVec OldError)
abbrev PairOutcome := Result (core.result.Result Unit NewError × ByteVec)

def program (fields : ByteVec → Slice U32 → PairOutcome)
 (frontier : ByteVec → Frontier → PairOutcome) : List Step → ByteVec → Outcome
 | [],out => ok (.Ok out)
 | .byte b::ss,out => do
   let next ← alloc.vec.Vec.push out b
   program fields frontier ss next
 | .words s::ss,out => nextPublic (mapPairOutcome (fields out s)) (program fields frontier ss)
 | .frontier f::ss,out => nextPublic (mapPairOutcome (frontier out f)) (program fields frontier ss)
 | .index n::ss,out => do
   let next ← alloc.vec.Vec.extend_from_slice core.clone.CloneU8 out
    (Array.to_slice (core.num.U64.to_le_bytes n))
   program fields frontier ss next

/-- Full packet substitution at every callee boundary, with error transport
and the same intermediate Vec. No successful-serializer premise. -/
theorem emitted (ss : List Step) (out : ByteVec) :
 program NHG_FieldSpec.fields
  pool_v1.pair_forest_semantic_terminal.r0.Public.public_bytes.frontier ss out =
 AspisR1PublicSerializer.Whole431.program ss out := by
 induction ss generalizing out with
 | nil => rfl
 | cons s ss ih =>
   cases s with
   | byte b =>
     simp only [program,AspisR1PublicSerializer.Whole431.program]
     cases call : alloc.vec.Vec.push out b with
     | fail e => rfl
     | div => rfl
     | ok next => exact ih next
   | index n =>
     simp only [program,AspisR1PublicSerializer.Whole431.program]
     cases call : alloc.vec.Vec.extend_from_slice core.clone.CloneU8 out
       (Array.to_slice (core.num.U64.to_le_bytes n)) with
     | fail e => rfl
     | div => rfl
     | ok next => exact ih next
   | words s =>
     simp only [program,AspisR1PublicSerializer.Whole431.program]
     rw [←SerializerLoop.fields_eq]
     cases call : AspisR1PublicSerializer.pool_v1.pair_forest_semantic_terminal.r0.Public.public_bytes.fields out s with
     | fail e => rfl
     | div => rfl
     | ok pair =>
       rcases pair with ⟨status,mid⟩
       cases status with
       | Err e => rfl
       | Ok u => cases u;exact ih mid
   | frontier f =>
     simp only [program,AspisR1PublicSerializer.Whole431.program]
     rw [←SerializerWhole.frontier_eq]
     cases call : AspisR1PublicSerializer.pool_v1.pair_forest_semantic_terminal.r0.Public.public_bytes.frontier out f with
     | fail e => rfl
     | div => rfl
     | ok pair =>
       rcases pair with ⟨status,mid⟩
       cases status with
       | Err e => rfl
       | Ok u => cases u;exact ih mid

theorem source (p : NHG_Serializer.Public) :
 p.public_bytes=NHG_Serializer.restore
  (program NHG_FieldSpec.fields
   pool_v1.pair_forest_semantic_terminal.r0.Public.public_bytes.frontier
   (sourceSteps (SerializerWhole.toOld p)) (alloc.vec.Vec.new U8)) := by
 rw [emitted]
 exact NHG_Serializer.source p

#print axioms emitted
#print axioms source
end AspisR1.NHG_ProducerPackets
