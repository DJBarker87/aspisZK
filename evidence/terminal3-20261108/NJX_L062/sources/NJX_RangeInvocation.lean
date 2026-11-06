import NJX_RangeFold
import NJB_ArrayCarrier
set_option autoImplicit false
noncomputable section
namespace AspisR1.NJX_RangeInvocation
open Aeneas Aeneas.Std Result
open FIv_NativeArithmetic (NQ)
open FIv_NativeValue (Canon decode K)
open NJX_RangeStep (State)
abbrev Openings := FIq_Native.state_only_poseidon.StateOnlyPoseidonOpenings
def views (o : Openings) : Fin 3 → Array NQ 16#usize := ![o.z,o.succ_z,o.xor12_z]
def xs (o : Openings) (view : Fin 3) (i : Fin 10) : NQ := NJB_ArrayCarrier.cell (views o view) ⟨i.val,by have h:=i.isLt;scalar_tac⟩
def zero : State := fun _=>FIq_Native.field.QM31.ZERO

theorem canonical (o : Openings) (hz : FIw_ArrayValue.canonical o.z)
 (hs : FIw_ArrayValue.canonical o.succ_z) (hx : FIw_ArrayValue.canonical o.xor12_z) :
 ∀ v i,Canon (xs o v i) := by
 intro v i
 have h : FIw_ArrayValue.canonical (views o v) := by fin_cases v <;> first|exact hz|exact hs|exact hx
 exact NJB_ArrayCarrier.canonical_cell _ h _

/-- Full source-order3×10range-loop invocation on SAME actual opening views,
ZERO33initialization, all intermediate33cell frames/canonicality. 233 SUPPORT;
reconstruction, conservation and both preweighted parent calls remain. -/
theorem source (o : Openings) (hz : FIw_ArrayValue.canonical o.z)
 (hs : FIw_ArrayValue.canonical o.succ_z) (hx : FIw_ArrayValue.canonical o.xor12_z) :
 ∃ a b c,
 NJX_RangeFold.run 0 (xs o 0) (List.finRange 10) zero=ok a ∧
 NJX_RangeFold.Trace 0 (xs o 0) (List.finRange 10) zero a ∧
 NJX_RangeFold.run 1 (xs o 1) (List.finRange 10) a=ok b ∧
 NJX_RangeFold.Trace 1 (xs o 1) (List.finRange 10) a b ∧
 NJX_RangeFold.run 2 (xs o 2) (List.finRange 10) b=ok c ∧
 NJX_RangeFold.Trace 2 (xs o 2) (List.finRange 10) b c ∧
 (∀ j,Canon (c j)) := by
 have h:=canonical o hz hs hx
 obtain ⟨a,ca,ta,ha,_⟩ := NJX_RangeFold.source 0 (xs o 0) (h 0) (List.finRange 10) zero (fun _=>FIv_NativeValue.zero.1)
 obtain ⟨b,cb,tb,hb,_⟩ := NJX_RangeFold.source 1 (xs o 1) (h 1) (List.finRange 10) a ha
 obtain ⟨c,cc,tc,hc,_⟩ := NJX_RangeFold.source 2 (xs o 2) (h 2) (List.finRange 10) b hb
 exact ⟨a,b,c,ca,ta,cb,tb,cc,tc,hc⟩
#print source
#print axioms canonical
#print axioms source
end AspisR1.NJX_RangeInvocation
end
