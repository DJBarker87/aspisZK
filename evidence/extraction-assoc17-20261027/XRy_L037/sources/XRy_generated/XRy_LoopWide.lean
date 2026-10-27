import XRy_WideMultiply
open Aeneas Aeneas.Std Result
open XRo_Join_Carriers
set_option autoImplicit false
namespace XRy_LoopWide
abbrev L := AspisR1LoopPowers.field.WideExact

def toLoop (x : C.E) : L :=
 ⟨⟨⟨x.c0.c0.a,x.c0.c0.b⟩,⟨x.c0.c1.a,x.c0.c1.b⟩⟩,
  ⟨⟨x.c1.c0.a,x.c1.c0.b⟩,⟨x.c1.c1.a,x.c1.c1.b⟩⟩⟩

theorem canonical (x : C.E) :
 XRy_WideMultiply.Canonical x ↔ AspisR1LoopPowers.Canonical (toLoop x) := Iff.rfl

theorem multiply (a b : C.E) (ha : XRy_WideMultiply.Canonical a) (hb : XRy_WideMultiply.Canonical b) :
 ∃ z, aspis_core.field.wide_exact.WideExact.mul a b = ok z ∧ XRy_WideMultiply.Canonical z ∧
 AspisR1LoopPowers.field.WideExact.mul (toLoop a) (toLoop b) = ok (toLoop z) := by
 obtain ⟨z,hz,hc,ht⟩ := XRy_WideMultiply.total a b ha hb
 refine ⟨z,hz,hc,?_⟩
 unfold AspisR1LoopPowers.field.WideExact.mul AspisR1PowersConcreteMul.sourceMul
 change (do let w ← AspisR1CurrentWideMul.field.wide_exact.WideExact.mul
              (XRy_WideMultiply.toWide a) (XRy_WideMultiply.toWide b)
            ok (AspisR1LoopPowers.fromOld (AspisR1PowersConcreteMul.fromWide w))) = _
 rw [ht,bind_tc_ok,bind_tc_ok]
 rfl

#print axioms canonical
#print axioms multiply
#print Aeneas.Std.Array.set
#print Aeneas.Std.loop.eq_def
end XRy_LoopWide
