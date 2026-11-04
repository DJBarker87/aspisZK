import NFT_PreparedSum3
import NFQ_PreparedMultiplier
set_option autoImplicit false
namespace NGA_Cache
open Aeneas Aeneas.Std Result AspisR1SelectedMaskProbe
abbrev Q := field.QM31
abbrev C := field.CM31
abbrev Cache := Array (Array U32 3#usize) 3#usize
abbrev Canonical := AspisR1.ExtractedMaskTowerAdd.CanonicalQM

/-- Exact frozen helper cache prelude, with no product operation. -/
def prelude (value : Q) : Result Cache := do
 let sum ← field.CM31.add value.c0 value.c1
 let a ← field.M31.add value.c0.a value.c0.b
 let b ← field.M31.add value.c1.a value.c1.b
 let c ← field.M31.add sum.a sum.b
 ok (Array.make 3#usize [Array.make 3#usize [value.c0.a,value.c0.b,a],
   Array.make 3#usize [value.c1.a,value.c1.b,b],Array.make 3#usize [sum.a,sum.b,c]])

theorem prelude_source (x : Q) (hx : Canonical x) :
 ∃ p : field.PreparedQm31Multiplier,
   field.PreparedQm31Multiplier.new x=ok p ∧ prelude x=ok p.components ∧
   NFQ_PreparedMultiplier.words p=NFQ_PreparedMultiplier.spec x := by
 obtain ⟨sum,hs,hsc,_,_⟩ := AspisR1.ExtractedMaskTowerAdd.current_cm_add_mod x.c0 x.c1 hx.1 hx.2
 obtain ⟨a,ha,_,_⟩ := AspisR1.ExtractedMaskM31AddSub.current_add_mod x.c0.a x.c0.b hx.1.1 hx.1.2
 obtain ⟨b,hb,_,_⟩ := AspisR1.ExtractedMaskM31AddSub.current_add_mod x.c1.a x.c1.b hx.2.1 hx.2.2
 obtain ⟨c,hc,_,_⟩ := AspisR1.ExtractedMaskM31AddSub.current_add_mod sum.a sum.b hsc.1 hsc.2
 obtain ⟨p,hp,words⟩ := NFQ_PreparedMultiplier.source x hx
 refine ⟨p,hp,?_,words⟩
 have hp' := hp
 simp only [field.PreparedQm31Multiplier.new,
   field.PreparedQm31Multiplier.new.closure.Insts.CoreOpsFunctionFnTupleCM31ArrayM313.call,
   ha,hb,hs,hc,bind_tc_ok] at hp'
 cases Result.ok.inj hp'
 simp only [prelude,ha,hb,hs,hc,bind_tc_ok]

#print axioms prelude_source
end NGA_Cache
