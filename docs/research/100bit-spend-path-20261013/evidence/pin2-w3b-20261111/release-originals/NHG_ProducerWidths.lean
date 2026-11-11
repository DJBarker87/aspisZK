import NHG_ProducerDomains
set_option autoImplicit false
open Aeneas Aeneas.Std Result AspisR1PublicPreparation
namespace AspisR1.NHG_ProducerWidths
open AspisR1PublicSerializer.Whole431

def Small : Step → Prop
 | .words s => s.length≤8
 | _ => True

theorem single_width (x : U32) : (single x).length≤8 := by
 change (1 : Nat)≤8
 decide

theorem widths (p : NHG_Serializer.Public) : ∀ s∈NHG_ProducerDomains.steps p,Small s := by
 cases p <;> intro s member <;>
  simp only [NHG_ProducerDomains.steps,SerializerWhole.toOld,sourceSteps,tailSteps,
    List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at member <;>
  rcases member with (h|h|h|h|h|h|h|h) | (h|h|h|h) <;> subst s <;>
  first | trivial | exact Nat.le_of_eq (NHG_Lengths.digest _) | exact single_width _

theorem fields (p : NHG_Serializer.Public) (v : Slice U32)
 (member : Step.words v∈NHG_ProducerDomains.steps p) : v.length≤8 := widths p (.words v) member

theorem field_domain (p : NHG_Serializer.Public) (pre rest : List Step)
 (v : Slice U32) (out : alloc.vec.Vec U8)
 (same : pre++Step.words v::rest=NHG_ProducerDomains.steps p)
 (bytes : out.val=pre.flatMap stepBytes) :
 1≤out.val.length ∧ v.length≤8 ∧ out.val.length+4*v.length≤1880 := by
 obtain ⟨nonempty,room⟩:=NHG_ProducerDomains.words_room p pre rest v out same bytes
 have member : Step.words v∈NHG_ProducerDomains.steps p := by
  rw [←same];simp
 exact ⟨nonempty,fields p v member,by omega⟩

theorem frontier_domain (p : NHG_Serializer.Public) (pre rest : List Step)
 (v : Array (Array U32 8#usize) 20#usize) (out : alloc.vec.Vec U8)
 (same : pre++Step.frontier v::rest=NHG_ProducerDomains.steps p)
 (bytes : out.val=pre.flatMap stepBytes) :
 1≤out.val.length ∧ out.val.length≤1240 := by
 have bounds:=NHG_ProducerDomains.frontier_room p pre rest v out same bytes
 exact ⟨bounds.1,by omega⟩

#print axioms single_width
#print axioms widths
#print axioms fields
#print axioms field_domain
#print axioms frontier_domain
end AspisR1.NHG_ProducerWidths
