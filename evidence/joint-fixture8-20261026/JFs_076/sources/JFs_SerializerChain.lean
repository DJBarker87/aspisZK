import JFs_SerializerLengths
set_option autoImplicit false
namespace AspisR1.JFs_SerializerChain
open Aeneas Aeneas.Std Result
open AspisR1PublicSerializer.FieldsRefinement431
open AspisR1PublicSerializer.Frontier431
open AspisR1PublicSerializer.pool_v1.pair_forest_semantic_terminal.r0.Public.public_bytes

theorem source (ss : List (Slice Field)) (out : ByteVec)
    (canon : canonical (ss.flatMap (fun s => s.val)))
    (cap : out.length+4*(ss.flatMap (fun s => s.val)).length≤Usize.max) :
    ∃ updated,chain ss out=ok (.Ok (),updated) ∧
      updated.val=out.val++encodeWords (ss.flatMap (fun s => s.val)) := by
  induction ss generalizing out with
  | nil => exact ⟨out,rfl,by simp [encodeWords]⟩
  | cons s ss ih =>
    have hc : canonical s.val := by
      intro x hx
      exact canon x (by simp only [List.flatMap_cons,List.mem_append];exact Or.inl hx)
    have hs : canonical (ss.flatMap (fun s => s.val)) := by
      intro x hx
      exact canon x (by simp only [List.flatMap_cons,List.mem_append];exact Or.inr hx)
    have capFirst : out.length+4*s.length≤Usize.max := by
      simp only [List.flatMap_cons,List.length_append] at cap
      change out.val.length+4*s.val.length≤Usize.max
      change out.val.length+4*(s.val.length+(ss.flatMap (fun s => s.val)).length)≤Usize.max at cap
      omega
    obtain ⟨middle,call,bytes⟩:=fields_canonical_append out s hc capFirst
    have middleLength : middle.length=out.length+4*s.length := by
      change middle.val.length=out.val.length+4*s.val.length
      rw [bytes,List.length_append,JFs_SerializerLengths.words]
    have capRest : middle.length+4*(ss.flatMap (fun s => s.val)).length≤Usize.max := by
      rw [middleLength]
      simp only [List.flatMap_cons,List.length_append] at cap
      change out.val.length+4*(s.val.length+(ss.flatMap (fun s => s.val)).length)≤Usize.max at cap
      change out.val.length+4*s.val.length+4*(ss.flatMap (fun s => s.val)).length≤Usize.max
      omega
    obtain ⟨updated,tail,contents⟩:=ih middle hs capRest
    refine ⟨updated,?_,?_⟩
    · simp only [uncurry,chain,thenCheck,call,bind_tc_ok,
        core.result.Result.Insts.CoreOpsTry.branch,tail]
    · simpa only [List.flatMap_cons,encodeWords,List.flatMap_append,bytes,List.append_assoc] using contents

#print axioms source
end AspisR1.JFs_SerializerChain
