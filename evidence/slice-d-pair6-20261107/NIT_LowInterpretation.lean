import NIT_PairComposition
set_option autoImplicit false
namespace AspisR1.NIT_LowInterpretation
open Aeneas Aeneas.Std Result LPi_FieldValues NIT_Cuts NIT_FieldInterpretation NIT_PairComposition

theorem limbs_injective : Function.Injective NGM_RoundScale.limbs := by
 intro a b h
 apply ew_injective
 simp only [NGM_RoundScale.limbs,List.cons.injEq] at h
 rcases h with ⟨h0,h1,h2,h3,h4,h5,h6,h7,_⟩
 exact Prod.ext (Prod.ext (Prod.ext h0 h1) (Prod.ext h2 h3))
  (Prod.ext (Prod.ext h4 h5) (Prod.ext h6 h7))

def Scale (input reply : E) : Prop :=
 NGM_RoundScale.limbs reply=(NGM_RoundScale.limbs input).map
  (fun word=>(word*134217728)%2147483647)

theorem scale (input reply : E) (law : Scale input reply) :
 FIo_Native.aspis_core.field.wide_exact.WideExact.mul_m31 input 134217728#u32=ok reply ∧
 canonE reply := by
 obtain ⟨out,run,canonical,value⟩ := NHX_LowScale.total input
 have same := limbs_injective (value.trans law.symm)
 subst out
 exact ⟨run,canonical⟩

theorem update_model {T : Type} {n : Usize} (before : Array T n) (i : Usize)
 (reply : T) (small : i.val<n.val) :
 Array.update before i reply=ok (NIT_ArrayFrames.put before i.val reply) :=
 NHI_ArrayCells.update before i reply small

/-- One Low window with every field call interpreted by its CLOSED packet;
the emitted body's index-routing association is kept separate. -/
theorem low_cell (ap0 ap1 : Powers) (i : Usize) (before after : LowCells) (l : Low)
 (cut : cutLow ap0 ap1 i.val before l after)
 (mulLaw : EMul l.a l.b l.product) (scaleLaw : Scale l.scale_a l.scaled) :
 (do
  let product ← FIo_Native.aspis_core.field.wide_exact.WideExact.mul
   (epick ap0 (perm (i.val%4))) (epick ap1 (perm (i.val/4)))
  let scalar ← FIo_Native.aspis_core.field.M31.mul FIo_Native.weights.QUARTER FIo_Native.weights.QUARTER
  let scaled ← FIo_Native.aspis_core.field.wide_exact.WideExact.mul_m31 product scalar
  Array.update before i scaled)=ok after ∧ canonical after := by
 have frame := low_frame ap0 ap1 i.val before after l cut
 rcases cut with ⟨small,cp0,cp1,cb,_,_,ma,mb,_,_,_,_,_,sa,_⟩
 have cm := em l.a l.b l.product
  (ma.symm ▸ epick_canonical ap0 cp0 _) (mb.symm ▸ epick_canonical ap1 cp1 _) mulLaw
 have cs := scale l.scale_a l.scaled scaleLaw
 rw [ma,mb] at cm
 rw [sa] at cs
 have update : Array.update before i l.scaled=ok after := by
  rw [frame]
  exact update_model before i l.scaled small
 refine ⟨?_,NHM_ArrayPreserve.canonical canonE before after i l.scaled cb cs.2 update⟩
 simp only [cm.1,NHX_LowScale.square,cs.1,update,bind_tc_ok]

#print axioms limbs_injective
#print axioms scale
#print axioms update_model
#print axioms low_cell
end AspisR1.NIT_LowInterpretation
