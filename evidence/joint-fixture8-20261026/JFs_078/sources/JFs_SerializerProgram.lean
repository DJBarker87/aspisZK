import JFs_SerializerFragment
set_option autoImplicit false
namespace AspisR1.JFs_SerializerProgram
open Aeneas Aeneas.Std Result
open AspisR1PublicSerializer.FieldsRefinement431
open AspisR1PublicSerializer.Frontier431
open AspisR1PublicSerializer.Whole431

theorem cons (s : Step) (ss : List Step) (out : ByteVec) :
    program (s::ss) out=nextPublic (JFs_SerializerFragment.run s out) (program ss) := by
  cases s with
  | byte b =>
    unfold program JFs_SerializerFragment.run nextPublic
    cases call : alloc.vec.Vec.push out b <;> rfl
  | words s => rfl
  | frontier f => rfl
  | index n =>
    unfold program JFs_SerializerFragment.run nextPublic
    cases call : alloc.vec.Vec.extend_from_slice core.clone.CloneU8 out
      (Array.to_slice (core.num.U64.to_le_bytes n)) <;> rfl

theorem source (ss : List Step) (out : ByteVec)
    (canon : canonical (ss.flatMap stepWords))
    (cap : out.length+(ss.flatMap stepBytes).length≤Usize.max) :
    ∃ updated,program ss out=ok (.Ok updated) ∧ updated.val=out.val++ss.flatMap stepBytes := by
  induction ss generalizing out with
  | nil => exact ⟨out,rfl,by simp⟩
  | cons s ss ih =>
    have hc : canonical (stepWords s) := by
      intro x hx
      exact canon x (by simp only [List.flatMap_cons,List.mem_append];exact Or.inl hx)
    have hs : canonical (ss.flatMap stepWords) := by
      intro x hx
      exact canon x (by simp only [List.flatMap_cons,List.mem_append];exact Or.inr hx)
    have capFirst : out.length+(stepBytes s).length≤Usize.max := by
      simp only [List.flatMap_cons,List.length_append] at cap
      omega
    obtain ⟨middle,call,bytes⟩:=JFs_SerializerFragment.source s out hc capFirst
    have middleLength : middle.length=out.length+(stepBytes s).length := by
      change middle.val.length=out.val.length+(stepBytes s).length
      rw [bytes,List.length_append]
    have capRest : middle.length+(ss.flatMap stepBytes).length≤Usize.max := by
      rw [middleLength]
      simp only [List.flatMap_cons,List.length_append] at cap
      omega
    obtain ⟨updated,tail,contents⟩:=ih middle hs capRest
    refine ⟨updated,?_,?_⟩
    · rw [cons]
      simp only [uncurry,nextPublic,call,bind_tc_ok,
        core.result.Result.Insts.CoreOpsTry.branch,tail]
    · simpa only [List.flatMap_cons,bytes,List.append_assoc] using contents

#print axioms cons
#print axioms source
end AspisR1.JFs_SerializerProgram
