import NHG_CopyFrame
set_option autoImplicit false
open Aeneas Aeneas.Std Result AspisR1PublicPreparation
namespace AspisR1.NHG_FieldSpec
open SerializerFields
abbrev fields := pool_v1.pair_forest_semantic_terminal.r0.Public.public_bytes.fields

theorem status_injective {A : Type} (a b : core.result.Result A NewError)
 (h : mapStatus a=mapStatus b) : a=b := by
 have v:=congrArg (fun s=>NHG_Serializer.restore (Result.ok s)) h
 change NHG_Serializer.restore (SerializerWhole.mapOutcome (.ok a))=
   NHG_Serializer.restore (SerializerWhole.mapOutcome (.ok b)) at v
 rw [NHG_Serializer.restore_map,NHG_Serializer.restore_map] at v
 exact Result.ok.inj v

/-- Complete status and exact mutated Vec for every field slice, including
first noncanonical rejection. No canonicality or successful-child hypothesis. -/
theorem source (out : ByteVec) (values : Slice U32)
 (cap : out.length+4*values.length≤Usize.max) :
 ∃ r, fields out values=ok r ∧
  (mapStatus r.1,r.2.val)=AspisR1PublicSerializer.FieldsRefinement431.specFields values.val out.val := by
 obtain ⟨r,call,spec⟩:=AspisR1PublicSerializer.FieldsRefinement431.fields_spec out values cap
 have transport:=SerializerLoop.fields_eq out values
 rw [call] at transport
 cases h : fields out values with
 | fail e => simp only [fields,h,mapPairOutcome] at transport; cases transport
 | div => simp only [fields,h,mapPairOutcome] at transport; cases transport
 | ok pair =>
   refine ⟨pair,h,?_⟩
   change ok r=mapPairOutcome (fields out values) at transport
   rw [h] at transport
   change ok r=ok (mapStatus pair.1,pair.2) at transport
   rw [Result.ok.inj transport] at spec
   exact spec

theorem reject (out : ByteVec) (values : Slice U32) (pre post : List U32) (x : U32)
 (same : values.val=pre++x::post)
 (canonical : AspisR1PublicSerializer.FieldsRefinement431.canonical pre)
 (bad : 2147483647≤x.val) (cap : out.length+4*values.length≤Usize.max) :
 ∃ out', fields out values=ok (.Err .Public,out') ∧
 out'.val=out.val++AspisR1PublicSerializer.FieldsRefinement431.encodeWords pre := by
 obtain ⟨⟨status,out'⟩,call,spec⟩:=source out values cap
 rw [same,AspisR1PublicSerializer.FieldsRefinement431.specFields_first_bad _ _ _ _ canonical bad] at spec
 have statusEq : status=core.result.Result.Err NewError.Public :=
  status_injective status (.Err .Public) (congrArg Prod.fst spec)
 subst status
 exact ⟨out',call,congrArg Prod.snd spec⟩

#print axioms status_injective
#print axioms source
#print axioms reject
end AspisR1.NHG_FieldSpec
