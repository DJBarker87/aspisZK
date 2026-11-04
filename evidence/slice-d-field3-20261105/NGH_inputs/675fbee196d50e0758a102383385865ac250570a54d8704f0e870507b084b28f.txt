import NGH_QSquareOps
import NGA_WideSquare
set_option autoImplicit false
noncomputable section
namespace NGH_WideBridge
open Aeneas Aeneas.Std Result AspisR1.FIo_FieldBridge

def run (x : NE) : Result NE :=
 NGA_WideSquare.G x FIo_Native.aspis_core.field.QM31.mul
 NGH_QSquareRef.run FIo_Native.aspis_core.field.wide_exact.mul_u

theorem same_square (x : NE) : run x=NGA_WideSquare.sourceModel x := by
 have h : NGH_QSquareRef.run=FIo_Native.aspis_core.field.QM31.square :=
   funext NGH_QSquareRef.model_eq
 rw [run,h]
 rfl

theorem source (x : NE) (hx : NGA_WideSquare.Canon x) :
 run x=FIo_Native.aspis_core.field.wide_exact.WideExact.mul x x :=
 (same_square x).trans (NGA_WideSquare.source x hx)

theorem cohort (x : NE) (hx : NGA_WideSquare.Canon x) :
 ∃ out, run x=ok out ∧ NGA_WideSquare.Canon out ∧
 NGA_WideSquare.decode out=NGA_WideSquare.decode x*NGA_WideSquare.decode x := by
 obtain ⟨out,ho,hc,hv⟩ := NGA_WideSquare.value x hx
 exact ⟨out,(same_square x).trans ho,hc,hv⟩
#print axioms same_square
#print axioms source
#print axioms cohort
end NGH_WideBridge
end
