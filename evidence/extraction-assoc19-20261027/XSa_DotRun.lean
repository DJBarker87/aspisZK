import XSa_DotReject
import XSa_FinishPair
open Aeneas Aeneas.Std Result
open XRo_Join_Carriers XSa_DotCarriers
set_option autoImplicit false
namespace XSa_DotRun
open AspisR1ClaimPreparedBridge
abbrev Range := core.ops.range.Range Usize
abbrev Coeff := Array C.E 29#usize

def cell (g : Coeff) (i : Usize) (hi : i.val<29) : C.E :=
 g.val[i.val]'(by have hg : g.val.length=29 := g.property; omega)
def canonical (g : Coeff) : Prop := ∀ i hi, XRy_WideMultiply.Canonical (cell g i hi)

def outcome : Option C.E → core.result.Result AspisR1CurrentPreparedClaim.Concrete.E AspisR1CurrentPreparedClaim.verifier.Error
 | none => .Err .Parse
 | some out => .Ok (toClaimE out)

def run {H : Type} (sem : C.Sem H) (s : Slice U8) (g : Coeff) (point : Nat) :
 Nat → Usize → Dot → Dot → Result (Option C.E)
 | 0,_,a,b => do let out ← XSa_FinishPair.finish a b; ok (some out)
 | n+1,i,a,b => do
   let q ← XRy_ClaimSelect.read (es sem) s point i.val
   if XSa_CheckedQ.valid q then do
     let v ← Array.index_usize g i
     let a' ← _root_.fast_pairing.canonical.Dot.push a (XRn_Join_toQ (eq v.c0)) (XRn_Join_toQ q)
     let b' ← _root_.fast_pairing.canonical.Dot.push b (XRn_Join_toQ (eq v.c1)) (XRn_Join_toQ q)
     let j ← i+1#usize
     run sem s g point n j a' b'
   else ok none

theorem coefficient (g : Coeff) (hg : canonical g) (i : Usize) (hi : i.val<29) :
 Array.index_usize g i=ok (cell g i hi) ∧ XRy_WideMultiply.Canonical (cell g i hi) ∧
 Array.index_usize (arr toClaimE g) i=ok (toClaimE (cell g i hi)) :=
 ⟨XRy_ArrayRead.read g i hi,hg i hi,XRy_ArrayRead.mapped toClaimE g i hi⟩

#print axioms coefficient
end XSa_DotRun
