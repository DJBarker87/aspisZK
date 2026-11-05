import NHG_PublicTranscript
import JFs_SerializerLengths
set_option autoImplicit false
open Aeneas Aeneas.Std Result AspisR1PublicPreparation
namespace AspisR1.NHG_Lengths
open AspisR1PublicSerializer.Whole431
open AspisR1PublicSerializer.FieldsRefinement431

theorem digest (a : Array U32 8#usize) : a.val.length=8 := a.property

theorem index (n : U64) : (core.num.U64.to_le_bytes n).val.length=8 :=
 (core.num.U64.to_le_bytes n).property

theorem source (p : NHG_Serializer.Public) :
 ((sourceSteps (SerializerWhole.toOld p)).flatMap stepBytes).length =
  match p with | .Transfer _ _ => 1455 | .Withdrawal _ _ => 1427 := by
 cases p <;>
 simp only [SerializerWhole.toOld,sourceSteps,tailSteps,List.flatMap_append,
  List.flatMap_cons,List.flatMap_nil,List.length_append,stepBytes,
  JFs_SerializerLengths.words,JFs_SerializerLengths.frontier_words,index,
  SerializerWhole.toTransfer,SerializerWhole.toWithdrawal,SerializerWhole.toTransition,
  digest,single,Array.to_slice,Array.make,List.length_cons,List.length_nil]

theorem bound (p : NHG_Serializer.Public) :
 ((sourceSteps (SerializerWhole.toOld p)).flatMap stepBytes).length≤1455 := by
 rw [source]; cases p <;> decide

theorem returned (p : NHG_Serializer.Public) (out : alloc.vec.Vec U8)
 (h : p.public_bytes=ok (.Ok out)) : out.val.length≤1455 := by
 rw [NHG_Serializer.bytes p out h]
 exact bound p

/-- Any actual instruction prefix with its exact produced Vec leaves room for
its next instruction. No canonicality or serializer-success assumption. -/
theorem prefix_room (p : NHG_Serializer.Public) (pre rest : List Step)
 (s : Step) (out : alloc.vec.Vec U8)
 (same : pre++s::rest=sourceSteps (SerializerWhole.toOld p))
 (bytes : out.val=pre.flatMap stepBytes) :
 out.length+(stepBytes s).length≤1455 := by
 have total:=bound p
 rw [←same,List.flatMap_append,List.flatMap_cons,List.length_append,List.length_append] at total
 change out.val.length+(stepBytes s).length≤1455
 rw [bytes]
 omega

theorem digest_domain (p : NHG_Serializer.Public) (out : alloc.vec.Vec U8)
 (h : p.public_bytes=ok (.Ok out)) (domain tag length pub root : Nat) :
 (NGX_SemanticRuntime.seedViews domain tag length pub root out.val.length).length≤9 ∧
 ∀ v∈NGX_SemanticRuntime.seedViews domain tag length pub root out.val.length,v.2≤57607 :=
 NGX_SemanticRuntime.seed_domain _ _ _ _ _ _ (by have:=returned p out h;omega)

#print axioms digest
#print axioms index
#print axioms source
#print axioms bound
#print axioms returned
#print axioms prefix_room
#print axioms digest_domain
end AspisR1.NHG_Lengths
