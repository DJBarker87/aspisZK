import NHX_ArraySlots
import NHX_FieldResults
set_option autoImplicit false
namespace NHX_HighReference
open Aeneas Aeneas.Std Result AspisR1 LPi_FieldValues
abbrev W := FIo_Native.weights.Weights
abbrev Row := NHX_HighDomain.Row
abbrev Parts := Array NE 7#usize
abbrev Powers := Array NE 4#usize
abbrev Reply := core.result.Result Unit FIo_Native.verifier.Error

def scale (row : Row) (ap0 ap1 : Powers) : Result NE := do
 let q0 ← Array.index_usize row 0#usize
 let a ← FIo_Native.weights.Weights.scalar_factor q0 ap0
 let q1 ← Array.index_usize row 1#usize
 let b ← FIo_Native.weights.Weights.scalar_factor q1 ap1
 FIo_Native.aspis_core.field.wide_exact.WideExact.mul a b

theorem scale_total (row : Row) (ap0 ap1 : Powers)
 (hr : ∀ d (hd : d<5),NHI_CellCanon.array (NHI_ScalarDomain.pick row d hd))
 (ha : ∀ x∈ap0.val,canonE x) (hb : ∀ x∈ap1.val,canonE x) :
 ∃ out,scale row ap0 ap1=ok out ∧ canonE out := by
 obtain ⟨q0,q1,a,b,out,i0,i1,sa,ca,sb,cb,ho,co⟩:=NHX_HighDomain.scale row ap0 ap1 hr ha hb
 exact ⟨out,by simp only [scale,i0,i1,sa,sb,ho,bind_tc_ok],co⟩

def row0 (w : W) : Row := NHI_ScalarDomain.pick w.factors 0 (by decide)
def row2 (w : W) : Row := NHI_ScalarDomain.pick w.factors 2 (by decide)
def coeff0 (w : W) : Array NQ 4#usize := NHI_ScalarDomain.pick (row0 w) 4 (by decide)
def coeff2 (w : W) : Array NQ 4#usize := NHI_ScalarDomain.pick (row2 w) 4 (by decide)

def reference (partials : Powers) (w : W) (ap0 ap1 : Powers) (parts : Parts) : Result (Reply×Parts) := do
 let r ← NHM_HighDot.reference partials (coeff0 w)
 let cf ← core.result.Result.Insts.CoreOpsTry.branch r
 match cf with
 | core.ops.control_flow.ControlFlow.Break residual=>do
  let rr ← core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
   Unit (core.convert.FromSame FIo_Native.verifier.Error) residual
  ok (rr,parts)
 | core.ops.control_flow.ControlFlow.Continue val=>do
  let a ← scale (row0 w) ap0 ap1
  let v1 ← FIo_Native.aspis_core.field.wide_exact.WideExact.mul a val
  let parts1:=NHI_ArrayCells.put parts 1#usize v1
  let r2 ← NHM_HighDot.reference partials (coeff2 w)
  let cf2 ← core.result.Result.Insts.CoreOpsTry.branch r2
  match cf2 with
  | core.ops.control_flow.ControlFlow.Break residual=>do
   let rr ← core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
    Unit (core.convert.FromSame FIo_Native.verifier.Error) residual
   ok (rr,parts1)
  | core.ops.control_flow.ControlFlow.Continue val2=>do
   let a2 ← scale (row2 w) ap0 ap1
   let v3 ← FIo_Native.aspis_core.field.wide_exact.WideExact.mul a2 val2
   ok (.Ok (),NHI_ArrayCells.put parts1 3#usize v3)

theorem bind_ext {A B : Type} (m : Result A) (f g : A→Result B)
 (same : ∀ x,f x=g x) : (m >>= f)=(m >>= g) := by
 rw [funext same]

theorem update3 (parts : Parts) (x : NE) :
 Array.update parts 3#usize x=ok (NHI_ArrayCells.put parts 3#usize x) :=
 NHI_ArrayCells.update parts 3#usize x (by decide)

/-- Reifies the emitted delayed mutable-slot continuation into the SAME
source-ordered parts[1]/parts[3] states; every error/nonreturn is retained. -/
theorem source (partials : Powers) (w : W) (ap0 ap1 : Powers) (parts : Parts) :
 FIo_Native.weights.shared_high partials w ap0 ap1 parts=reference partials w ap0 ap1 parts := by
 have ir0:Array.index_usize w.factors 0#usize=ok (row0 w):=NHI_ScalarDomain.index w.factors 0#usize (by decide)
 have ir2:Array.index_usize w.factors 2#usize=ok (row2 w):=NHI_ScalarDomain.index w.factors 2#usize (by decide)
 have ic0:Array.index_usize (row0 w) 4#usize=ok (coeff0 w):=NHI_ScalarDomain.index (row0 w) 4#usize (by decide)
 have ic2:Array.index_usize (row2 w) 4#usize=ok (coeff2 w):=NHI_ScalarDomain.index (row2 w) 4#usize (by decide)
 rw [NHM_SharedHigh.cohort]
 unfold NHM_SharedHigh.reference reference scale
 simp only [ir0,ir2,ic0,ic2,NHX_ArraySlots.mutable_slot parts 1#usize (by decide),update3,bind_assoc_eq,bind_tc_ok]
 apply bind_ext
 intro r
 apply bind_ext
 intro cf
 cases cf with
 | Break residual=>rfl
 | Continue val=>
  repeat' (apply bind_ext;intro x)
  first | rfl | (cases x <;> rfl)

#print axioms bind_ext
#print axioms scale_total
#print axioms update3
#print axioms source
end NHX_HighReference
