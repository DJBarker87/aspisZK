import NGA_CanonicalInjective
set_option autoImplicit false
noncomputable section
namespace NGA_WideSquare
open Aeneas Aeneas.Std Result AspisR1.FIo_FieldBridge
open AspisR1CurrentWide.Proof
abbrev Canon := AspisR1.FIo_WideValues.Canon
abbrev decode (x : NE) := decodeWide (wide x)

/-- Frozen square caller with exactly the four NFT opaque sites substituted.
The two real QM additions remain in their original source order. -/
def G (x : NE) (mul : NQ → NQ → Result NQ) (square mulU : NQ → Result NQ) : Result NE := do
 let cross ← mul x.c0 x.c1
 let aa ← square x.c0
 let bb ← square x.c1
 let u ← mulU bb
 let lo ← FIo_Native.aspis_core.field.QM31.add aa u
 let hi ← FIo_Native.aspis_core.field.QM31.add cross cross
 ok ⟨lo,hi⟩

def sourceModel (x : NE) : Result NE := G x FIo_Native.aspis_core.field.QM31.mul
 FIo_Native.aspis_core.field.QM31.square FIo_Native.aspis_core.field.wide_exact.mul_u

theorem value (x : NE) (hx : Canon x) :
 ∃ out, sourceModel x=ok out ∧ Canon out ∧ decode out=decode x*decode x := by
 obtain ⟨cross,hcross,cc,vcross⟩ := NGA_NativeOps.product x.c0 x.c1 hx.1 hx.2
 obtain ⟨aa,haa,ca,vaa⟩ := NGA_NativeOps.square x.c0 hx.1
 obtain ⟨bb,hbb,cb,vbb⟩ := NGA_NativeOps.square x.c1 hx.2
 obtain ⟨u,hu,cu,vu⟩ := NGA_NativeOps.mul_u bb cb
 obtain ⟨lo,hlo,cl,vlo⟩ := NGA_NativeOps.addition aa u ca cu
 obtain ⟨hi,hhi,ch,vhi⟩ := NGA_NativeOps.addition cross cross cc cc
 refine ⟨⟨lo,hi⟩,?_,⟨cl,ch⟩,?_⟩
 · simp only [sourceModel,G,hcross,haa,hbb,hu,hlo,hhi,bind_tc_ok]
 · apply QuadraticAlgebra.ext
   · change NGA_NativeOps.decode lo = _
     simp only [decode,decodeWide,wide,QuadraticAlgebra.re_mul]
     rw [vlo,vaa,vu,vbb]
     ring
   · change NGA_NativeOps.decode hi = _
     simp only [decode,decodeWide,wide,QuadraticAlgebra.im_mul]
     rw [vhi,vcross]
     ring

/-- Full canonical record equality, not merely equality after decoding. -/
theorem source (x : NE) (hx : Canon x) : sourceModel x=
 FIo_Native.aspis_core.field.wide_exact.WideExact.mul x x := by
 obtain ⟨out,ho,co,vo⟩ := value x hx
 obtain ⟨product,hp⟩ := AspisR1.NFN_LPi_Total.wide_mul x x
 obtain ⟨cp,vp⟩ := AspisR1.FIo_WideMulValues.mul x x product hx hx hp
 have same : out=product := NGA_CanonicalInjective.wide out product co cp (vo.trans vp.symm)
 rw [ho,hp,same]

#print axioms value
#print axioms source
end NGA_WideSquare
end
