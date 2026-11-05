import NHG_ProducerWidths
import NHG_ProducerPackets
set_option autoImplicit false
open Aeneas Aeneas.Std Result AspisR1PublicPreparation
namespace AspisR1.NHG_ProgramChain
open AspisR1PublicSerializer.Whole431
abbrev Output := core.result.Result SerializerFields.ByteVec SerializerFields.OldError

def resume (rest : List Step) (r : Output) : Result Output :=
 match r with | .Err e=>ok (.Err e) | .Ok out=>program rest out

/-- Native cuts at source callee boundaries compose for every error, failure
and divergence; this equality never assumes a successful final serializer. -/
theorem append (pre rest : List Step) (out : SerializerFields.ByteVec) :
 program (pre++rest) out=(do let result←program pre out;resume rest result) := by
 induction pre generalizing out with
 | nil => rfl
 | cons s pre ih =>
   cases s with
   | byte b =>
     simp only [List.cons_append,program]
     cases call : alloc.vec.Vec.push out b with
     | fail e => rfl
     | div => rfl
     | ok next => exact ih next
   | index n =>
     simp only [List.cons_append,program]
     cases call : alloc.vec.Vec.extend_from_slice core.clone.CloneU8 out
       (Array.to_slice (core.num.U64.to_le_bytes n)) with
     | fail e => rfl
     | div => rfl
     | ok next => exact ih next
   | words s =>
     simp only [List.cons_append,program]
     cases call : AspisR1PublicSerializer.pool_v1.pair_forest_semantic_terminal.r0.Public.public_bytes.fields out s with
     | fail e => rfl
     | div => rfl
     | ok pair =>
       rcases pair with ⟨status,mid⟩
       cases status with
       | Err e => rfl
       | Ok u => cases u;exact ih mid
   | frontier f =>
     simp only [List.cons_append,program]
     cases call : AspisR1PublicSerializer.pool_v1.pair_forest_semantic_terminal.r0.Public.public_bytes.frontier out f with
     | fail e => rfl
     | div => rfl
     | ok pair =>
       rcases pair with ⟨status,mid⟩
       cases status with
       | Err e => rfl
       | Ok u => cases u;exact ih mid

theorem history_bytes (pre : List Step) (out : SerializerFields.ByteVec)
 (history : program pre (alloc.vec.Vec.new U8)=ok (.Ok out)) :
 out.val=pre.flatMap stepBytes := by
 have bytes:=(program_success pre (alloc.vec.Vec.new U8) out history).2
 simpa only [alloc.vec.Vec.new,List.nil_append] using bytes

/-- A reached local cut has a successful PREFIX. Later steps may still
reject. The actual prefix's bytes establish the next callee's native domain. -/
theorem reached_field (p : NHG_Serializer.Public) (pre rest : List Step)
 (v : Slice U32) (out : SerializerFields.ByteVec)
 (same : pre++Step.words v::rest=NHG_ProducerDomains.steps p)
 (history : program pre (alloc.vec.Vec.new U8)=ok (.Ok out)) :
 1≤out.val.length ∧ v.length≤8 ∧ out.val.length+4*v.length≤1880 :=
 NHG_ProducerWidths.field_domain p pre rest v out same (history_bytes pre out history)

theorem reached_frontier (p : NHG_Serializer.Public) (pre rest : List Step)
 (v : Array (Array U32 8#usize) 20#usize) (out : SerializerFields.ByteVec)
 (same : pre++Step.frontier v::rest=NHG_ProducerDomains.steps p)
 (history : program pre (alloc.vec.Vec.new U8)=ok (.Ok out)) :
 1≤out.val.length ∧ out.val.length≤1240 :=
 NHG_ProducerWidths.frontier_domain p pre rest v out same (history_bytes pre out history)

#print axioms append
#print axioms history_bytes
#print axioms reached_field
#print axioms reached_frontier
end AspisR1.NHG_ProgramChain
