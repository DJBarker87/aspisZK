import NHG_FrontierPackets
set_option autoImplicit false
open Aeneas Aeneas.Std Result AspisR1PublicPreparation
namespace AspisR1.NHG_ProducerDomains
open AspisR1PublicSerializer.Whole431 AspisR1PublicSerializer.FieldsRefinement431

abbrev steps (p : NHG_Serializer.Public) := sourceSteps (SerializerWhole.toOld p)

theorem first (p : NHG_Serializer.Public) : ∃ b rest,steps p=Step.byte b::rest := by
 cases p <;> exact ⟨_,_,rfl⟩

theorem prefix_nonempty (p : NHG_Serializer.Public) (pre rest : List Step) (s : Step)
 (same : pre++s::rest=steps p) (entered : pre≠[]) :
 1≤(pre.flatMap stepBytes).length := by
 obtain ⟨b,tail,head⟩:=first p
 cases pre with
 | nil => exact False.elim (entered rfl)
 | cons x xs =>
   rw [head] at same
   change x::(xs++s::rest)=Step.byte b::tail at same
   have hx:= (List.cons.inj same).1
   rw [hx]
   simp only [List.flatMap_cons,stepBytes,List.length_append,List.length_cons,List.length_nil]
   omega

theorem words_noninitial (p : NHG_Serializer.Public) (pre rest : List Step) (v : Slice U32)
 (same : pre++Step.words v::rest=steps p) : pre≠[] := by
 intro empty;subst pre
 obtain ⟨b,tail,head⟩:=first p
 rw [head] at same
 cases (List.cons.inj same).1

theorem frontier_noninitial (p : NHG_Serializer.Public) (pre rest : List Step)
 (v : Array (Array U32 8#usize) 20#usize)
 (same : pre++Step.frontier v::rest=steps p) : pre≠[] := by
 intro empty;subst pre
 obtain ⟨b,tail,head⟩:=first p
 rw [head] at same
 cases (List.cons.inj same).1

theorem words_room (p : NHG_Serializer.Public) (pre rest : List Step) (v : Slice U32)
 (out : alloc.vec.Vec U8) (same : pre++Step.words v::rest=steps p)
 (bytes : out.val=pre.flatMap stepBytes) :
 1≤out.val.length ∧ out.val.length+4*v.length≤1455 := by
 have room:=NHG_Lengths.prefix_room p pre rest (.words v) out same bytes
 have nonempty:=prefix_nonempty p pre rest (.words v) same (words_noninitial p pre rest v same)
 rw [←bytes] at nonempty
 change 1≤out.val.length ∧ out.val.length+4*v.length≤1455
 refine ⟨nonempty,?_⟩
 simpa only [stepBytes,JFs_SerializerLengths.words] using room

theorem frontier_room (p : NHG_Serializer.Public) (pre rest : List Step)
 (v : Array (Array U32 8#usize) 20#usize) (out : alloc.vec.Vec U8)
 (same : pre++Step.frontier v::rest=steps p) (bytes : out.val=pre.flatMap stepBytes) :
 1≤out.val.length ∧ out.val.length≤815 := by
 have room:=NHG_Lengths.prefix_room p pre rest (.frontier v) out same bytes
 have nonempty:=prefix_nonempty p pre rest (.frontier v) same (frontier_noninitial p pre rest v same)
 rw [←bytes] at nonempty
 have width : (stepBytes (.frontier v)).length=640 := JFs_SerializerLengths.frontier_bytes v
 change out.val.length+(stepBytes (.frontier v)).length≤1455 at room
 rw [width] at room
 exact ⟨nonempty,by omega⟩

#print axioms first
#print axioms prefix_nonempty
#print axioms words_noninitial
#print axioms frontier_noninitial
#print axioms words_room
#print axioms frontier_room
end AspisR1.NHG_ProducerDomains
