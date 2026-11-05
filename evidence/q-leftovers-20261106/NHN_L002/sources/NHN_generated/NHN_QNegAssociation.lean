import NHH_QNeg
import NFT_WideNeg
set_option autoImplicit false
namespace NHN_QNegAssociation
open Aeneas Aeneas.Std Result
abbrev Q := NHH_QNeg.Q
abbrev CQ := AspisR1CurrentWide.field.QM31
abbrev CC := AspisR1CurrentWide.field.CM31

def cm (x : NHH_QNeg.C) : CC := ⟨x.a,x.b⟩
def receiver (x : Q) : CQ := ⟨cm x.c0,cm x.c1⟩
def zero : CQ := ⟨⟨0#u32,0#u32⟩,⟨0#u32,0#u32⟩⟩

theorem scalar (x : U32) (hx : x.val<2147483647) :
 AspisR1CurrentWide.field.M31.sub 0#u32 x=NFG_CheckedFieldRef.field.M31.neg x := by
 rw [NFT_NegSub.scalar x hx]
 simp only [AspisR1SelectedMaskProbe.field.M31.neg,NFG_CheckedFieldRef.field.M31.neg,
 AspisR1SelectedMaskProbe.field.P,NFG_CheckedFieldRef.field.P]

/-- The SAME four receiver limbs, at the adopted zero-minus endpoint used by
NFT_WideNeg.source. This is an existing cohort subtraction, not a neg stand-in. -/
theorem association (x : Q) (hx : NHH_QNeg.Canon x) :
 (do let out ← NFG_CheckedFieldRef.field.QM31.neg x;ok (receiver out))=
 AspisR1CurrentWide.field.QM31.sub zero (receiver x) := by
 rcases hx with ⟨⟨ha,hb⟩,⟨hc,hd⟩⟩
 simp only [NFG_CheckedFieldRef.field.QM31.neg,NFG_CheckedFieldRef.field.CM31.neg,
 AspisR1CurrentWide.field.QM31.sub,AspisR1CurrentWide.field.CM31.sub,zero,receiver,cm,
 scalar _ ha,scalar _ hb,scalar _ hc,scalar _ hd,bind_assoc_eq,bind_tc_ok]

/-- Both native receiver coordinates of the existing WideExact negation
consumer are associated to its actual adopted cohort endpoint. -/
theorem enclosing (x y : Q) (hx : NHH_QNeg.Canon x) (hy : NHH_QNeg.Canon y) :
 (do let a ← NFG_CheckedFieldRef.field.QM31.neg x
     let b ← NFG_CheckedFieldRef.field.QM31.neg y
     ok (AspisR1CurrentWide.field.wide_exact.WideExact.mk (receiver a) (receiver b)))=
 AspisR1CurrentWide.field.wide_exact.WideExact.sub NFT_WideNeg.zero
  ⟨receiver x,receiver y⟩ := by
 simp only [AspisR1CurrentWide.field.wide_exact.WideExact.sub,NFT_WideNeg.zero]
 rw [←association x hx,←association y hy]
 simp only [bind_assoc_eq,bind_tc_ok]

#print axioms scalar
#print axioms association
#print axioms enclosing
end NHN_QNegAssociation
