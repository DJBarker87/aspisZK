import S9ActualReduceWordSourceV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result
open AspisR1S9ProductionPairCutV1
namespace AspisR1S9ActualFinishWordFormulaV1
open AspisR1S9ActualReduceWordSourceV1
abbrev W := aspis_core.field.wide_exact.WideExact

def wordWide (a b c d e f g h : U64) : W :=
  {c0:={c0:={a:=word a,b:=word b},c1:={a:=word c,b:=word d}},
   c1:={c0:={a:=word e,b:=word f},c1:={a:=word g,b:=word h}}}
def nativeWords (w : W) : List U32 :=
  [w.c0.c0.a,w.c0.c0.b,w.c0.c1.a,w.c0.c1.b,
   w.c1.c0.a,w.c1.c0.b,w.c1.c1.a,w.c1.c1.b]
private theorem ix4_0 (a b c d : U32) : Array.index_usize (Array.make 4#usize [a,b,c,d]) 0#usize = .ok a := rfl
private theorem ix4_1 (a b c d : U32) : Array.index_usize (Array.make 4#usize [a,b,c,d]) 1#usize = .ok b := rfl
private theorem ix4_2 (a b c d : U32) : Array.index_usize (Array.make 4#usize [a,b,c,d]) 2#usize = .ok c := rfl
private theorem ix4_3 (a b c d : U32) : Array.index_usize (Array.make 4#usize [a,b,c,d]) 3#usize = .ok d := rfl
private theorem ix8_0 (a b c d e f g h : U32) : Array.index_usize (Array.make 8#usize [a,b,c,d,e,f,g,h]) 0#usize = .ok a := rfl
private theorem ix8_1 (a b c d e f g h : U32) : Array.index_usize (Array.make 8#usize [a,b,c,d,e,f,g,h]) 1#usize = .ok b := rfl
private theorem ix8_2 (a b c d e f g h : U32) : Array.index_usize (Array.make 8#usize [a,b,c,d,e,f,g,h]) 2#usize = .ok c := rfl
private theorem ix8_3 (a b c d e f g h : U32) : Array.index_usize (Array.make 8#usize [a,b,c,d,e,f,g,h]) 3#usize = .ok d := rfl
private theorem ix8_4 (a b c d e f g h : U32) : Array.index_usize (Array.make 8#usize [a,b,c,d,e,f,g,h]) 4#usize = .ok e := rfl
private theorem ix8_5 (a b c d e f g h : U32) : Array.index_usize (Array.make 8#usize [a,b,c,d,e,f,g,h]) 5#usize = .ok f := rfl
private theorem ix8_6 (a b c d e f g h : U32) : Array.index_usize (Array.make 8#usize [a,b,c,d,e,f,g,h]) 6#usize = .ok g := rfl
private theorem ix8_7 (a b c d e f g h : U32) : Array.index_usize (Array.make 8#usize [a,b,c,d,e,f,g,h]) 7#usize = .ok h := rfl
private theorem word_bound (x : U64) : ¬ word x ≥ aspis_core.field.P := by
  unfold aspis_core.field.P
  change ¬ 2147483647 ≤ (word x).val
  rw [AspisR1CanonicalDotFinish.Proof.canonicalWord_val]
  simpa only [AspisV8R17.RawReducer.P] using
    (Nat.not_le_of_gt (Nat.mod_lt x.val (show 0<AspisV8R17.RawReducer.P by decide)))

/-- Each actual explicit Dot.finish call computes four retained mathematical
canonical words. This uses no physical Rust Array.map/IntoIter refinement. -/
theorem actual_dot_finish_four (a b c d : U64) :
    fast_pairing.canonical.Dot.finish ⟨Array.make 4#usize [a,b,c,d]⟩ =
      .ok (Array.make 4#usize [word a,word b,word c,word d]) := by
  have h0 : Array.index_usize (Array.make 4#usize [a,b,c,d]) 0#usize = .ok a := rfl
  have h1 : Array.index_usize (Array.make 4#usize [a,b,c,d]) 1#usize = .ok b := rfl
  have h2 : Array.index_usize (Array.make 4#usize [a,b,c,d]) 2#usize = .ok c := rfl
  have h3 : Array.index_usize (Array.make 4#usize [a,b,c,d]) 3#usize = .ok d := rfl
  simp only [fast_pairing.canonical.Dot.finish,h0,h1,h2,h3,actual_reduce_word,bind_tc_ok]

private theorem from_words (a b c d e f g h : U64) :
    aspis_core.field.wide_exact.WideExact.from_limbs
      (Array.make 8#usize [word a,word b,word c,word d,word e,word f,word g,word h]) =
      .ok (some (wordWide a b c d e f g h)) := by
  simp only [aspis_core.field.wide_exact.WideExact.from_limbs,
    ix8_0,ix8_1,ix8_2,ix8_3,ix8_4,ix8_5,ix8_6,ix8_7,bind_tc_ok,
    if_neg (word_bound a),if_neg (word_bound b),if_neg (word_bound c),if_neg (word_bound d),if_neg (word_bound e),if_neg (word_bound f),if_neg (word_bound g),if_neg (word_bound h)]
  rfl

/-- Universal actual finish formula for arbitrary accumulator cells/count.
All eight from_limbs checks are discharged by the same reduced words. -/
theorem actual_finish_four_four (a b c d e f g h : U64) (n : Usize) :
    fast_pairing.EbyKDot.finish
      {c0:=⟨Array.make 4#usize [a,b,c,d]⟩,
       c1:=⟨Array.make 4#usize [e,f,g,h]⟩,count:=n} =
      .ok (wordWide a b c d e f g h) := by
  unfold fast_pairing.EbyKDot.finish
  simp only [actual_dot_finish_four,bind_tc_ok,fast_pairing.canonical.Q.limbs,
    ix4_0,ix4_1,ix4_2,ix4_3,from_words,core.option.Option.unwrap]
  rfl

/-- SAME accepted current finish exposes exactly the retained mathematical
word reducer for each original accumulator cell. List.map here specifies the
mathematical output list; no old physical stdlib map source law is assumed. -/
theorem actual_finish_success_word_list (self : fast_pairing.EbyKDot) (out : W)
    (h : fast_pairing.EbyKDot.finish self = .ok out) :
    nativeWords out = (self.c0.sums.val++self.c1.sums.val).map word := by
  rcases self with ⟨⟨lo⟩,⟨hi⟩,n⟩
  obtain ⟨a,b,c,d,hlo⟩ := List.length_eq_four.mp lo.property
  obtain ⟨e,f,g,hh,hhi⟩ := List.length_eq_four.mp hi.property
  have hlo' : lo=Array.make 4#usize [a,b,c,d] := Subtype.ext hlo
  have hhi' : hi=Array.make 4#usize [e,f,g,hh] := Subtype.ext hhi
  subst lo
  subst hi
  have known := actual_finish_four_four a b c d e f g hh n
  have he : wordWide a b c d e f g hh=out := Result.ok.inj (known.symm.trans h)
  subst out
  rfl

#print axioms actual_dot_finish_four
#print axioms actual_finish_four_four
#print axioms actual_finish_success_word_list
end AspisR1S9ActualFinishWordFormulaV1
