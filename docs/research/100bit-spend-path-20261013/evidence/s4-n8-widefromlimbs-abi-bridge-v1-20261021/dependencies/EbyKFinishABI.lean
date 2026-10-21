import AspisR1EbyKFinish.Funs
import CanonicalDotFinishSemantics
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1EbyKFinish.Proof
open AspisV8R17.RawReducer
abbrev OldDot := AspisR1CanonicalDotFinish.canonical.Dot

def toOldDot (d : canonical.Dot) : OldDot := {sums:=d.sums}

theorem canonical_reduce_same (x : U64) :
    canonical.reduce x = AspisR1CanonicalDotFinish.canonical.reduce x := by
  unfold canonical.reduce AspisR1CanonicalDotFinish.canonical.reduce
    canonical.P AspisR1CanonicalDotFinish.canonical.P
  rfl

theorem canonical_dot_finish_same (d : canonical.Dot) :
    canonical.Dot.finish d = AspisR1CanonicalDotFinish.canonical.Dot.finish (toOldDot d) := by
  have he : canonical.reduce=AspisR1CanonicalDotFinish.canonical.reduce := funext canonical_reduce_same
  unfold canonical.Dot.finish AspisR1CanonicalDotFinish.canonical.Dot.finish toOldDot
  rw [he]

def wideFromParts (a b c d e f g h : U32) : field.wide_exact.WideExact :=
  {c0:={c0:={a:=a,b:=b},c1:={a:=c,b:=d}},c1:={c0:={a:=e,b:=f},c1:={a:=g,b:=h}}}

theorem canonical_from_limbs (a b c d e f g h : U32)
    (Ca : a.val<P) (Cb : b.val<P) (Cc : c.val<P) (Cd : d.val<P)
    (Ce : e.val<P) (Cf : f.val<P) (Cg : g.val<P) (Ch : h.val<P) :
    field.wide_exact.WideExact.from_limbs (Array.make 8#usize [a,b,c,d,e,f,g,h]) =
      .ok (some (wideFromParts a b c d e f g h)) := by
  have ha : ¬ a >= field.P := by change ¬ field.P.val ≤ a.val;unfold field.P;change ¬ P ≤ a.val;omega
  have hb : ¬ b >= field.P := by change ¬ field.P.val ≤ b.val;unfold field.P;change ¬ P ≤ b.val;omega
  have hc : ¬ c >= field.P := by change ¬ field.P.val ≤ c.val;unfold field.P;change ¬ P ≤ c.val;omega
  have hd : ¬ d >= field.P := by change ¬ field.P.val ≤ d.val;unfold field.P;change ¬ P ≤ d.val;omega
  have he : ¬ e >= field.P := by change ¬ field.P.val ≤ e.val;unfold field.P;change ¬ P ≤ e.val;omega
  have hf : ¬ f >= field.P := by change ¬ field.P.val ≤ f.val;unfold field.P;change ¬ P ≤ f.val;omega
  have hg : ¬ g >= field.P := by change ¬ field.P.val ≤ g.val;unfold field.P;change ¬ P ≤ g.val;omega
  have hh : ¬ h >= field.P := by change ¬ field.P.val ≤ h.val;unfold field.P;change ¬ P ≤ h.val;omega
  have h0 : Array.index_usize (Array.make 8#usize [a,b,c,d,e,f,g,h]) 0#usize = .ok a := rfl
  have h1 : Array.index_usize (Array.make 8#usize [a,b,c,d,e,f,g,h]) 1#usize = .ok b := rfl
  have h2 : Array.index_usize (Array.make 8#usize [a,b,c,d,e,f,g,h]) 2#usize = .ok c := rfl
  have h3 : Array.index_usize (Array.make 8#usize [a,b,c,d,e,f,g,h]) 3#usize = .ok d := rfl
  have h4 : Array.index_usize (Array.make 8#usize [a,b,c,d,e,f,g,h]) 4#usize = .ok e := rfl
  have h5 : Array.index_usize (Array.make 8#usize [a,b,c,d,e,f,g,h]) 5#usize = .ok f := rfl
  have h6 : Array.index_usize (Array.make 8#usize [a,b,c,d,e,f,g,h]) 6#usize = .ok g := rfl
  have h7 : Array.index_usize (Array.make 8#usize [a,b,c,d,e,f,g,h]) 7#usize = .ok h := rfl
  simp only [field.wide_exact.WideExact.from_limbs,h0,h1,h2,h3,h4,h5,h6,h7,
    bind_tc_ok,ha,hb,hc,hd,he,hf,hg,hh,if_false]
  rfl

#print axioms canonical_reduce_same
#print axioms canonical_dot_finish_same
#print axioms canonical_from_limbs
end AspisR1EbyKFinish.Proof
