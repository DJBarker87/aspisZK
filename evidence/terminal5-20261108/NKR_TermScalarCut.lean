import NKR_TermScalarInvocation
import NKI_AppendCut
set_option autoImplicit false
noncomputable section
namespace AspisR1.NKR_TermScalarCut
open Aeneas Aeneas.Std Result FIq_Native
open FIv_NativeArithmetic (NQ)
open NKI_InitialPrefix (Public Openings Selectors)
open NKR_TermScalarInvocation (Packed Packet amount)
open NKI_AppendCut (Event)
def kinds : Fin 12 → Nat := ![5,2,6,0,6,0,6,0,6,5,2,0]
def left {pub o s before} (p : Packet pub o s before) : Fin 12 → NQ :=
 ![FIw_ScalarArithmetic.lifted pub.asset_id,NJB_ArrayCarrier.cell o.z ⟨1,by decide⟩,
  field.QM31.ZERO,p.selected 0,field.QM31.ZERO,p.selected 1,field.QM31.ZERO,p.selected 2,
  field.QM31.ZERO,FIw_ScalarArithmetic.lifted (amount pub),NJB_ArrayCarrier.cell o.z ⟨10,by decide⟩,p.selected 3]
def right {pub o s before} (p : Packet pub o s before) : Fin 12 → NQ :=
 ![field.QM31.ZERO,FIw_ScalarArithmetic.lifted pub.asset_id,field.QM31.ZERO,p.difference,
  field.QM31.ZERO,p.difference,field.QM31.ZERO,p.difference,field.QM31.ZERO,field.QM31.ZERO,
  FIw_ScalarArithmetic.lifted (amount pub),p.withdrawalDifference]
/-- The native lift event records the raw M31 embedding input, whose value is
identically the emitted lifted scalar. No arithmetic output is added to a cut. -/
structure Observation where
 events : Fin 12 → Event
 selectors : Fin 4 → Selectors
 rows : Fin 4 → Usize
 variant : pool_v1.pair_forest_semantic_terminal.CompiledVariant
 present : Bool
 scalarArgs : Fin 4 → NQ
 packedBefore : Packed
 values : Array NQ 2#usize
 after : Packed
 calls : Nat
 start : Nat

def Cut (pub : Public) (o : Openings) (s : Selectors) (before : Packed)
 (p : Packet pub o s before) (ob : Observation) : Prop :=
 (∀ i,(ob.events i).kind=kinds i ∧ (ob.events i).left=left p i ∧ (ob.events i).right=right p i) ∧
 (∀ g,ob.selectors g=s ∧ ob.rows g=NKR_TermScalarInvocation.rows g) ∧
 ob.variant=pub.variant ∧ ob.present=core.option.Option.is_some pub.withdrawal_amount ∧
 ob.scalarArgs=p.products ∧ ob.packedBefore=before ∧ ob.values=p.scalars ∧ ob.after=p.out ∧ ob.calls=14 ∧ ob.start=92

def observations {pub o s before} (p : Packet pub o s before) : Observation :=
 ⟨(fun i=>⟨kinds i,left p i,right p i⟩),(fun _=>s),NKR_TermScalarInvocation.rows,pub.variant,
  core.option.Option.is_some pub.withdrawal_amount,p.products,before,p.scalars,p.out,14,92⟩

theorem source (pub : Public) (o : Openings) (s : Selectors) (before : Packed)
 (hz : FIw_ArrayValue.canonical o.z) (hh : FIw_ArrayValue.canonical s.high)
 (hl : FIw_ArrayValue.canonical s.low) (hb : FIw_ArrayValue.canonical before)
 (ha : pub.asset_id.val<2147483647) (hm : (amount pub).val<2147483647) :
 ∃ p : Packet pub o s before,FIw_ScalarSuffix.run pub o s before=ok p.out ∧
 Cut pub o s before p (observations p) := by
 obtain ⟨p,call⟩:=NKR_TermScalarInvocation.source pub o s before hz hh hl hb ha hm
 exact ⟨p,call,⟨fun _=>⟨rfl,rfl,rfl⟩,fun _=>⟨rfl,rfl⟩,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩⟩
#print source
#print axioms source
end AspisR1.NKR_TermScalarCut
end
