import NKI_InitialPrefix
set_option autoImplicit false
noncomputable section
namespace AspisR1.NKI_InitialTotal
open Aeneas Aeneas.Std Result WP FIq_Native
open FIv_NativeValue (Canon)
open FIw_ArrayValue (canonical)
open NKI_InitialPrefix (Public Openings Selectors Tail)
def Canonical (t : Tail) : Prop := canonical t.initial ∧ Canon t.low ∧ Canon t.fixed ∧ Canon t.two ∧ Canon t.eight ∧ Canon t.nodes
/-- Total full initial-array/scalar prefix for arbitrary SAME public.variant,
not the historical fixed fixture p. All generated std operations are pinned. -/
theorem source (p : Public) (o : Openings) (s : Selectors)
 (hz : canonical o.z) (hh : canonical s.high) (hl : canonical s.low) :
 NKI_InitialPrefix.run p o s ⦃ out=>Canonical out ⦄ := by
 have zero:=FIv_NativeValue.zero.1
 unfold NKI_InitialPrefix.run poseidon2.RATE
 step*
 all_goals first
  | (subst_vars;exact FIx_ScheduleIndices.node_bounds)
  | (unfold Canonical;exact ⟨by assumption,by assumption,by assumption,by assumption,by assumption,by assumption⟩)
#print axioms source
end AspisR1.NKI_InitialTotal
end
