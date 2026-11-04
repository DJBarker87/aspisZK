import NGA_Cache
import NFT_ChannelModel
set_option autoImplicit false
namespace NGA_CacheDomain
open Aeneas Aeneas.Std Result AspisR1SelectedMaskProbe
abbrev Cache := NGA_Cache.Cache
abbrev Q := NGA_Cache.Q
abbrev Canonical := NGA_Cache.Canonical

def Bounded (c : Cache) : Prop := ∀ row ∈ c.val, ∀ word ∈ row.val, word.val<2147483647

theorem row_bounded (x : field.CM31) (hx : AspisR1.ExtractedMaskTowerAdd.CanonicalCM x)
 (a : AspisR1.ExtractedMaskPreparedState.Component)
 (ha : AspisR1.ExtractedMaskPreparedState.ComponentFor a x) :
 ∀ word ∈ a.val, word.val<2147483647 := by
 obtain ⟨s,hs,_,hc⟩ := ha
 subst a
 intro word hw
 change word ∈ [x.a,x.b,s] at hw
 simp only [List.mem_cons,List.mem_singleton] at hw
 rcases hw with rfl | rfl | rfl
 · exact hx.1
 · exact hx.2
 · exact hc

theorem prepared_bounded (p : field.PreparedQm31Multiplier) (x : Q)
 (hx : Canonical x) (hp : AspisR1.ExtractedMaskPreparedState.PreparedFor p x) : Bounded p.components := by
 obtain ⟨t,a,b,c,_,ht,ha,hb,hc,hp⟩ := hp
 intro row hr
 rw [hp] at hr
 change row ∈ [a,b,c] at hr
 simp only [List.mem_cons,List.mem_singleton] at hr
 rcases hr with rfl | rfl | rfl
 · exact row_bounded x.c0 hx.1 a ha
 · exact row_bounded x.c1 hx.2 b hb
 · exact row_bounded t ht c hc

theorem source (x : Q) (hx : Canonical x) :
 ∃ c : Cache, NGA_Cache.prelude x=ok c ∧ Bounded c ∧
   ∃ p : field.PreparedQm31Multiplier, field.PreparedQm31Multiplier.new x=ok p ∧
     c=p.components ∧ NFQ_PreparedMultiplier.words p=NFQ_PreparedMultiplier.spec x := by
 obtain ⟨p,hp,hc,words⟩ := NGA_Cache.prelude_source x hx
 obtain ⟨p',hp',domain⟩ := AspisR1.ExtractedMaskPreparedState.current_prepared_new x hx
 have same : p'=p := Result.ok.inj (hp'.symm.trans hp)
 subst p'
 exact ⟨p.components,hc,prepared_bounded p x hx domain,p,hp,rfl,words⟩

#print axioms row_bounded
#print axioms prepared_bounded
#print axioms source
end NGA_CacheDomain
