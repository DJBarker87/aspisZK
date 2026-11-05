import NHG_FieldSpec
set_option autoImplicit false
open Aeneas Aeneas.Std Result AspisR1PublicPreparation
namespace AspisR1.NHG_FieldBounds
open AspisR1PublicSerializer.FieldsRefinement431

theorem raw_length (xs : List U32) (out : List U8) :
 out.length≤(specFields xs out).2.length ∧
 (specFields xs out).2.length≤out.length+4*xs.length := by
 induction xs generalizing out with
 | nil => constructor <;> change out.length≤out.length <;> exact Nat.le_refl _
 | cons x xs ih =>
   simp only [specFields]
   split
   · simp only [List.length_cons];constructor <;> omega
   · have step:=ih (out++wordBytes x)
     rw [List.length_append,wordBytes_length] at step
     simp only [List.length_cons]
     constructor <;> omega

theorem raw_prefix (xs : List U32) (out : List U8) :
 ∃ suffix,(specFields xs out).2=out++suffix := by
 induction xs generalizing out with
 | nil => exact ⟨[],by simp only [specFields,List.append_nil]⟩
 | cons x xs ih =>
   simp only [specFields]
   split
   · exact ⟨[],by simp only [List.append_nil]⟩
   · obtain ⟨tail,ht⟩:=ih (out++wordBytes x)
     exact ⟨wordBytes x++tail,by simpa only [List.append_assoc] using ht⟩

/-- The child envelope used by native frontier cuts is DERIVED for every
raw input, even first-bad rejection. The same Vec's prior prefix is retained. -/
theorem source (out : alloc.vec.Vec U8) (values : Slice U32)
 (cap : out.length+4*values.length≤Usize.max) :
 ∃ r,NHG_FieldSpec.fields out values=ok r ∧
 out.length≤r.2.length ∧ r.2.length≤out.length+4*values.length ∧
 ∃ suffix,r.2.val=out.val++suffix := by
 obtain ⟨r,call,spec⟩:=NHG_FieldSpec.source out values cap
 have bytes : r.2.val=(specFields values.val out.val).2 := congrArg Prod.snd spec
 have bounds:=raw_length values.val out.val
 obtain ⟨tail,frame⟩:=raw_prefix values.val out.val
 refine ⟨r,call,?_,?_,tail,bytes.trans frame⟩
 · change out.val.length≤r.2.val.length
   rw [bytes];exact bounds.1
 · change r.2.val.length≤out.val.length+4*values.val.length
   rw [bytes];exact bounds.2

#print axioms raw_length
#print axioms raw_prefix
#print axioms source
end AspisR1.NHG_FieldBounds
