import NKI_ValueFrames
import NKI_ValueFields
import NKI_ConservationInvocation
import NKI_AppendCut
set_option autoImplicit false
noncomputable section
namespace AspisR1.NKI_ValueCuts
open Aeneas Aeneas.Std Result FIq_Native
open FIv_NativeArithmetic (NQ)
open NKI_ValuePrefix (Openings Selectors)
open NKI_ValueTrace (Locals)
open NKI_AppendCut (Event)
def sumLeft (l : Locals) : Fin 3 → NQ := ![field.QM31.ZERO,l.q1,l.q3]
def sumRight (l : Locals) : Fin 3 → NQ := ![l.q,l.q2,l.q4]
def tailKind : Fin 8 → Nat := ![11,11,10,1,11,10,1,2]
def tailLeft (l : Locals) : Fin 8 → NQ := ![field.QM31.ZERO,field.QM31.ZERO,l.q6,l.q5,field.QM31.ZERO,l.q9,l.q8,l.q11]
def tailRight (l : Locals) : Fin 8 → NQ := ![field.QM31.ZERO,field.QM31.ZERO,FIw_ScalarArithmetic.lifted 1024#u32,l.q7,field.QM31.ZERO,FIw_ScalarArithmetic.lifted 1048576#u32,l.q10,l.reconstructed]
def consKind : Fin 5 → Nat := ![2,2,0,2,0]
def consLeft (c : NKI_ConservationInvocation.Locals) : Fin 5 → NQ := ![c.q15,c.q17,c.conservation_selector,c.q21,c.conservation_selector]
def consRight (c : NKI_ConservationInvocation.Locals) : Fin 5 → NQ := ![c.q16,c.q18,c.q19,c.q22,c.q23]
structure Observations where
 rows : Fin 3 → Usize
 high : Fin 3 → Fin 64 → NQ
 low : Fin 3 → Fin 16 → NQ
 sums : Fin 3 → Event
 sumOut : NQ
 views : Fin 3 → Array NQ 16#usize
 tail : Fin 8 → Event
 rangeOut : Array NQ 33#usize
 sharedStart : Nat
 sharedSelector : NQ
 sharedBefore : Array NQ 24#usize
 sharedValues : Array NQ 33#usize
 sharedAfter : Array NQ 24#usize
 conservation : Fin 5 → Event
 finalStart : Nat
 finalBefore : Array NQ 24#usize
 finalValues : Array NQ 2#usize
 finalAfter : Array NQ 24#usize
/-- K003/004 windowed full receiver selector prologue; K005/006 global8call
reconstruction; NJX range/49shared/conservation/82final windows. Exact native
assertion transcriptions at the SAME source cuts, complete poststates. -/
def Cut (packed : Array NQ 24#usize) (o : Openings) (s : Selectors) (l : Locals)
 (c : NKI_ConservationInvocation.Locals) (middle out : Array NQ 24#usize)
 (ob : Observations) (counts : Fin 6 → Nat) : Prop :=
 counts=![3,3,8,1,5,1] ∧
 ob.rows=NKI_ValueFields.row ∧
 (∀ g i,ob.high g i=NJB_ArrayCarrier.cell s.high i) ∧
 (∀ g i,ob.low g i=NJB_ArrayCarrier.cell s.low i) ∧
 (∀ g,(ob.sums g).kind=1 ∧ (ob.sums g).left=sumLeft l g ∧ (ob.sums g).right=sumRight l g) ∧ ob.sumOut=l.range_selector ∧
 ob.views=![o.z,o.succ_z,o.xor12_z] ∧
 (∀ i,(ob.tail i).kind=tailKind i ∧ (ob.tail i).left=tailLeft l i ∧ (ob.tail i).right=tailRight l i) ∧
 (∀ j,NJB_ArrayCarrier.cell ob.rangeOut j=if j.val=30 then l.q12 else if j.val=31 then l.q13 else if j.val=32 then l.q14 else NJB_ArrayCarrier.cell l.range3 j) ∧
 ob.sharedStart=49 ∧ ob.sharedSelector=l.range_selector ∧ ob.sharedBefore=packed ∧ ob.sharedValues=l.range6 ∧ ob.sharedAfter=middle ∧
 (∀ i,(ob.conservation i).kind=consKind i ∧ (ob.conservation i).left=consLeft c i ∧ (ob.conservation i).right=consRight c i) ∧
 ob.finalStart=82 ∧ ob.finalBefore=middle ∧ ob.finalValues=Array.make 2#usize [c.q20,c.q24] ∧ ob.finalAfter=out

def observations (packed : Array NQ 24#usize) (o : Openings) (s : Selectors) (l : Locals)
 (c : NKI_ConservationInvocation.Locals) (middle out : Array NQ 24#usize) : Observations :=
 {rows:=NKI_ValueFields.row
  high:=fun _=>NJB_ArrayCarrier.cell s.high
  low:=fun _=>NJB_ArrayCarrier.cell s.low
  sums:=fun g=>⟨1,sumLeft l g,sumRight l g⟩
  sumOut:=l.range_selector
  views:=![o.z,o.succ_z,o.xor12_z]
  tail:=fun i=>⟨tailKind i,tailLeft l i,tailRight l i⟩
  rangeOut:=l.range6
  sharedStart:=49
  sharedSelector:=l.range_selector
  sharedBefore:=packed
  sharedValues:=l.range6
  sharedAfter:=middle
  conservation:=fun i=>⟨consKind i,consLeft c i,consRight c i⟩
  finalStart:=82
  finalBefore:=middle
  finalValues:=Array.make 2#usize [c.q20,c.q24]
  finalAfter:=out}

theorem source (packed : Array NQ 24#usize) (o : Openings) (s : Selectors) (l : Locals)
 (c : NKI_ConservationInvocation.Locals) (middle out : Array NQ 24#usize)
 (calls : NKI_ValueTrace.Clauses o s l) :
 Cut packed o s l c middle out (observations packed o s l c middle out) ![3,3,8,1,5,1] := by
 exact ⟨rfl,rfl,fun _ _=>rfl,fun _ _=>rfl,fun _=>⟨rfl,rfl,rfl⟩,rfl,rfl,fun _=>⟨rfl,rfl,rfl⟩,
  (NKI_ValueFrames.source o s l calls).2.2,rfl,rfl,rfl,rfl,rfl,fun _=>⟨rfl,rfl,rfl⟩,rfl,rfl,rfl,rfl⟩
#print Cut
#print axioms source
end AspisR1.NKI_ValueCuts
end
