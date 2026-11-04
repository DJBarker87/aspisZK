import NFT_WideReference.Funs
import NFT_NegSub
set_option autoImplicit false
namespace NFT_WideNeg
open Aeneas Aeneas.Std Result
abbrev E := AspisR1CurrentWide.field.wide_exact.WideExact

def words (x : E) : Array U32 8#usize := Array.make 8#usize
  [x.c0.c0.a,x.c0.c0.b,x.c0.c1.a,x.c0.c1.b,x.c1.c0.a,x.c1.c0.b,x.c1.c1.a,x.c1.c1.b]
def zero : E := ⟨⟨⟨0#u32,0#u32⟩,⟨0#u32,0#u32⟩⟩,⟨⟨0#u32,0#u32⟩,⟨0#u32,0#u32⟩⟩⟩
def Canonical (x : E) : Prop :=
  x.c0.c0.a.val<2147483647 ∧ x.c0.c0.b.val<2147483647 ∧
  x.c0.c1.a.val<2147483647 ∧ x.c0.c1.b.val<2147483647 ∧
  x.c1.c0.a.val<2147483647 ∧ x.c1.c0.b.val<2147483647 ∧
  x.c1.c1.a.val<2147483647 ∧ x.c1.c1.b.val<2147483647

theorem scalar (x : U32) (canonical : x.val<2147483647) :
    NFT_WideReference.neg_ref x=AspisR1SelectedMaskProbe.field.M31.neg x :=
  NFT_NegWord.source x canonical

/-- The extracted full native reference computes the adopted tower's zero-minus
operation on the same eight limbs, with no inner successful-call hypothesis. -/
theorem source (x : E) (canonical : Canonical x) :
    ∃ z : E, NFT_WideReference.wide_neg_ref (words x)=ok (words z) ∧
      AspisR1CurrentWide.field.wide_exact.WideExact.sub zero x=ok z ∧ Canonical z := by
  rcases canonical with ⟨ha,hb,hc,hd,he,hf,hg,hh⟩
  obtain ⟨a,ra,va,ca⟩:=NFQ_FieldLaws.neg_value x.c0.c0.a ha
  obtain ⟨b,rb,vb,cb⟩:=NFQ_FieldLaws.neg_value x.c0.c0.b hb
  obtain ⟨c,rc,vc,cc⟩:=NFQ_FieldLaws.neg_value x.c0.c1.a hc
  obtain ⟨d,rd,vd,cd⟩:=NFQ_FieldLaws.neg_value x.c0.c1.b hd
  obtain ⟨e,re,ve,ce⟩:=NFQ_FieldLaws.neg_value x.c1.c0.a he
  obtain ⟨f,rf,vf,cf⟩:=NFQ_FieldLaws.neg_value x.c1.c0.b hf
  obtain ⟨g,rg,vg,cg⟩:=NFQ_FieldLaws.neg_value x.c1.c1.a hg
  obtain ⟨h,rh,vh,ch⟩:=NFQ_FieldLaws.neg_value x.c1.c1.b hh
  refine ⟨⟨⟨⟨a,b⟩,⟨c,d⟩⟩,⟨⟨e,f⟩,⟨g,h⟩⟩⟩,?_,?_,⟨ca,cb,cc,cd,ce,cf,cg,ch⟩⟩
  · simp [NFT_WideReference.wide_neg_ref,words,Array.index_usize,Array.make,
      scalar _ ha,scalar _ hb,scalar _ hc,scalar _ hd,scalar _ he,scalar _ hf,scalar _ hg,scalar _ hh,
      ra,rb,rc,rd,re,rf,rg,rh]
  · simp only [AspisR1CurrentWide.field.wide_exact.WideExact.sub,
      AspisR1CurrentWide.field.QM31.sub,AspisR1CurrentWide.field.CM31.sub,zero,
      NFT_NegSub.scalar _ ha,NFT_NegSub.scalar _ hb,NFT_NegSub.scalar _ hc,NFT_NegSub.scalar _ hd,
      NFT_NegSub.scalar _ he,NFT_NegSub.scalar _ hf,NFT_NegSub.scalar _ hg,NFT_NegSub.scalar _ hh,
      ra,rb,rc,rd,re,rf,rg,rh,bind_tc_ok]

#print axioms scalar
#print axioms source
end NFT_WideNeg
