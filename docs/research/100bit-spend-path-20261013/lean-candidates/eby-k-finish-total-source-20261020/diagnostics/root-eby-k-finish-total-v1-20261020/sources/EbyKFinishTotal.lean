import EbyKFinishABI
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1EbyKFinish.Proof
open AspisV8R17.RawReducer
abbrev word := AspisR1CanonicalDotFinish.Proof.canonicalWord

theorem dot_finish_four (a b c d : U64) :
    canonical.Dot.finish {sums:=Array.make 4#usize [a,b,c,d]} =
      .ok (Array.make 4#usize [word a,word b,word c,word d]) := by
  rw [canonical_dot_finish_same]
  obtain ⟨out,hout,hvals,_⟩ := AspisR1CanonicalDotFinish.Proof.canonical_dot_finish_total
    (toOldDot {sums:=Array.make 4#usize [a,b,c,d]})
  have he : out=Array.make 4#usize [word a,word b,word c,word d] := Subtype.ext hvals
  rw [←he]
  exact hout

theorem word_canonical (x : U64) : (word x).val<P := by
  rw [AspisR1CanonicalDotFinish.Proof.canonicalWord_val]
  exact Nat.mod_lt _ (by decide)

theorem finish_eight (count : Usize) (a b c d e f g h : U64) :
    EbyKDot.finish {c0:={sums:=Array.make 4#usize [a,b,c,d]},
      c1:={sums:=Array.make 4#usize [e,f,g,h]},count:=count} =
      .ok (wideFromParts (word a) (word b) (word c) (word d)
        (word e) (word f) (word g) (word h)) := by
  have hwide := canonical_from_limbs (word a) (word b) (word c) (word d)
    (word e) (word f) (word g) (word h) (word_canonical a) (word_canonical b)
    (word_canonical c) (word_canonical d) (word_canonical e) (word_canonical f)
    (word_canonical g) (word_canonical h)
  have lo0 : Array.index_usize (Array.make 4#usize [word a,word b,word c,word d]) 0#usize = .ok (word a) := rfl
  have lo1 : Array.index_usize (Array.make 4#usize [word a,word b,word c,word d]) 1#usize = .ok (word b) := rfl
  have lo2 : Array.index_usize (Array.make 4#usize [word a,word b,word c,word d]) 2#usize = .ok (word c) := rfl
  have lo3 : Array.index_usize (Array.make 4#usize [word a,word b,word c,word d]) 3#usize = .ok (word d) := rfl
  have hi0 : Array.index_usize (Array.make 4#usize [word e,word f,word g,word h]) 0#usize = .ok (word e) := rfl
  have hi1 : Array.index_usize (Array.make 4#usize [word e,word f,word g,word h]) 1#usize = .ok (word f) := rfl
  have hi2 : Array.index_usize (Array.make 4#usize [word e,word f,word g,word h]) 2#usize = .ok (word g) := rfl
  have hi3 : Array.index_usize (Array.make 4#usize [word e,word f,word g,word h]) 3#usize = .ok (word h) := rfl
  simp only [EbyKDot.finish,dot_finish_four,canonical.Q.limbs,bind_tc_ok,
    lo0,lo1,lo2,lo3,hi0,hi1,hi2,hi3,hwide]
  rfl

def finishLimbs (out : field.wide_exact.WideExact) : List U32 :=
  [out.c0.c0.a,out.c0.c0.b,out.c0.c1.a,out.c0.c1.b,
   out.c1.c0.a,out.c1.c0.b,out.c1.c1.a,out.c1.c1.b]

theorem eby_finish_total (self : EbyKDot) :
    ∃ out, EbyKDot.finish self = .ok out ∧
      finishLimbs out = (self.c0.sums.val++self.c1.sums.val).map word ∧
      ∀ v ∈ finishLimbs out, v.val<P := by
  cases self with
  | mk c0 c1 count =>
    cases c0 with
    | mk lo =>
      cases c1 with
      | mk hi =>
        obtain ⟨a,b,c,d,hlo⟩ := List.length_eq_four.mp lo.property
        obtain ⟨e,f,g,h,hhi⟩ := List.length_eq_four.mp hi.property
        have helo : lo=Array.make 4#usize [a,b,c,d] := Subtype.ext hlo
        have hehi : hi=Array.make 4#usize [e,f,g,h] := Subtype.ext hhi
        subst lo
        subst hi
        refine ⟨wideFromParts (word a) (word b) (word c) (word d)
          (word e) (word f) (word g) (word h),finish_eight count a b c d e f g h,rfl,?_⟩
        intro v hv
        simp only [finishLimbs,wideFromParts,List.mem_cons,List.not_mem_nil,or_false] at hv
        rcases hv with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
        all_goals exact word_canonical _

theorem eby_finish_entry_total (self : EbyKDot) :
    ∃ out, eby_finish_entry self = .ok out ∧
      finishLimbs out=(self.c0.sums.val++self.c1.sums.val).map word ∧
      ∀ v ∈ finishLimbs out, v.val<P :=
  eby_finish_total self

#print axioms dot_finish_four
#print axioms word_canonical
#print axioms finish_eight
#print axioms eby_finish_total
#print axioms eby_finish_entry_total
end AspisR1EbyKFinish.Proof
