import XSa_RawFolds
open Aeneas Aeneas.Std Result
open XRo_Join_Carriers
set_option autoImplicit false
namespace XSa_RawModel
open AspisR1.R22RawQmProductResidues

theorem model (a b : E.Q) (ha : XSa_QRawTotal.canonical a) (hb : XSa_QRawTotal.canonical b) :
 XRn_Join_raw (XRn_Join_toQ a) (XRn_Join_toQ b) =
 [rawC0 a.c0.a.val a.c0.b.val a.c1.a.val a.c1.b.val b.c0.a.val b.c0.b.val b.c1.a.val b.c1.b.val,
  rawC1 a.c0.a.val a.c0.b.val a.c1.a.val a.c1.b.val b.c0.a.val b.c0.b.val b.c1.a.val b.c1.b.val,
  rawC2 a.c0.a.val a.c0.b.val a.c1.a.val a.c1.b.val b.c0.a.val b.c0.b.val b.c1.a.val b.c1.b.val,
  rawC3 a.c0.a.val a.c0.b.val a.c1.a.val a.c1.b.val b.c0.a.val b.c0.b.val b.c1.a.val b.c1.b.val] := by
 let A:=a.c0.a.val; let B:=a.c0.b.val; let C:=a.c1.a.val; let D:=a.c1.b.val
 let E:=b.c0.a.val; let F:=b.c0.b.val; let G:=b.c1.a.val; let H:=b.c1.b.val
 have ha' : A≤2147483646 ∧ B≤2147483646 ∧ C≤2147483646 ∧ D≤2147483646 := by
   unfold XSa_QRawTotal.canonical at ha; dsimp [A,B,C,D]; omega
 have hb' : E≤2147483646 ∧ F≤2147483646 ∧ G≤2147483646 ∧ H≤2147483646 := by
   unfold XSa_QRawTotal.canonical at hb; dsimp [E,F,G,H]; omega
 have guards := AspisR1S5CurrentRepin.canonical_raw_range_guards A B C D E F G H
   ha'.1 ha'.2.1 ha'.2.2.1 ha'.2.2.2 hb'.1 hb'.2.1 hb'.2.2.1 hb'.2.2.2
 dsimp only at guards
 norm_num only [Nat.reducePow,Nat.reduceSub,Nat.reduceMul] at guards
 rcases guards with ⟨hcg,hdh,hch,hae,hbf,h0u,h0all,hvsub,h1ab,h1u,h1v,h2ag,h2all,hbh,hdf,h3ab,h3c,h3d,h2u,h2v⟩
 have huv := XSa_RawFolds.uv C D G H ha'.2.2.1 ha'.2.2.2 hb'.2.2.1 hb'.2.2.2
 change
 [XRn_Join_sub64 (XRn_Join_wrap64 (XRn_Join_sub64 (XRn_Join_wrap64 (A*E+2147483647*2147483647)) (B*F)+2* _+3*2147483647)) _,
  XRn_Join_wrap64 (A*F+B*E+_+2*_),
  XRn_Join_sub64 (XRn_Join_sub64 (XRn_Join_wrap64 (A*G+C*E+2*(2147483647*2147483647))) (B*H)) (D*F),
  XRn_Join_wrap64 (A*H+B*G+C*F+D*E)] = _
 rw [huv.1,huv.2]
 rw [XSa_RawWrap.wrap _ hae,XSa_RawWrap.sub _ _ hae hbf,
   XSa_RawWrap.wrap _ h0all,XSa_RawWrap.sub _ _ h0all hvsub,
   XSa_RawWrap.wrap _ h1v,XSa_RawWrap.wrap _ h2all,
   XSa_RawWrap.sub _ _ h2all hbh,XSa_RawWrap.sub _ _ (by omega) hdf,
   XSa_RawWrap.wrap _ h3d]
 simp only [rawC0,rawC1,rawC2,rawC3,rawU,rawV,AspisV8R17.RawReducer.foldBits_eq_fold31]
 rfl

#print axioms model
end XSa_RawModel
