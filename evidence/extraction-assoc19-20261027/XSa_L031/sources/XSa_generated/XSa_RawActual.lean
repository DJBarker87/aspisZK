import XSa_RawModel
open Aeneas Aeneas.Std Result
open XRo_Join_Carriers
set_option autoImplicit false
namespace XSa_RawActual

theorem bound (q : E.Q) (hq : XSa_QRawTotal.canonical q) (i : Nat) (hi : i<4) :
 ((XRn_Join_toQ q).val[i]!).val≤2^31-2 := by
 unfold XSa_QRawTotal.canonical at hq
 interval_cases i <;> simp only [XRn_Join_toQ,Array.make,List.getElem!_cons_zero,List.getElem!_cons_succ] <;> omega

theorem actual (a b : E.Q) (ha : XSa_QRawTotal.canonical a) (hb : XSa_QRawTotal.canonical b) :
 ∃ out, AspisR1EbyKPushDecodedProductUpdate.QRaw (XRn_Join_toQ a) (XRn_Join_toQ b)=ok out ∧
 out.val.map UScalar.val=XRn_Join_raw (XRn_Join_toQ a) (XRn_Join_toQ b) := by
 obtain ⟨out,call⟩ := XSa_QRawTotal.total a b ha hb
 obtain ⟨na,nb,nc,nd,ne,nf,ng,nh,r0,r1,r2,r3,shape,h0,h1,h2,h3,ha0,ha1,ha2,ha3,hb0,hb1,hb2,hb3⟩ :=
   AspisR1QRawGeneratedPushConnectionV2.source_raw_output_coefficients_v2
     (XRn_Join_toQ a) (XRn_Join_toQ b) out call
     (bound a ha 0 (by omega)) (bound a ha 1 (by omega))
     (bound a ha 2 (by omega)) (bound a ha 3 (by omega))
     (bound b hb 0 (by omega)) (bound b hb 1 (by omega))
     (bound b hb 2 (by omega)) (bound b hb 3 (by omega))
 rw [ha0,ha1,ha2,ha3,hb0,hb1,hb2,hb3] at h0 h1 h2 h3
 simp only [XRn_Join_toQ,Array.make,List.getElem!_cons_zero,List.getElem!_cons_succ] at h0 h1 h2 h3
 refine ⟨out,call,?_⟩
 rw [shape]
 simp only [Array.make,List.map_cons,List.map_nil,h0,h1,h2,h3]
 exact (XSa_RawModel.model a b ha hb).symm

#print axioms bound
#print axioms actual
end XSa_RawActual
