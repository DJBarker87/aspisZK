import NKI_InitialFrames
import NKI_SelectorWindow
import NKI_AppendCut
set_option autoImplicit false
noncomputable section
namespace AspisR1.NKI_InitialCuts
open Aeneas Aeneas.Std Result FIq_Native
open FIv_NativeArithmetic (NQ)
open FIv_PreparedNew (NP)
open NKI_InitialPrefix (Public Openings Selectors)
open NKI_InitialInvocation (Locals)
open NKI_AppendCut (Event)
def proKind : Fin 12 → Nat := ![7,1,1,1,8,1,1,0,0,3,1,3]
def proLeft (l : Locals) : Fin 12 → NQ := ![field.QM31.ZERO,l.q,l.q2,l.q4,l.q6,l.first_common,l.q10,l.q9,l.q9,l.full_initial_selector,l.full_initial_selector,l.q12]
def proRight (l : Locals) : Fin 12 → NQ := ![field.QM31.ZERO,l.q1,l.q3,l.q5,l.q7,l.transfer_first,l.fixed,l.q11,l.nodes,field.QM31.ZERO,l.rate_initial_selector,field.QM31.ZERO]
def constantKind : Fin 12 → Nat := ![1,1,10,10,1,10,1,10,10,1,10,1]
def lift (x : U32) : NQ := FIw_ScalarArithmetic.lifted x
def constantLeft (l : Locals) : Fin 12 → NQ := ![l.q1,l.q13,l.q,l.note_first,l.q14,l.q3,l.q16,l.q,l.note_first,l.q18,l.q3,l.q20]
def constantRight (l : Locals) : Fin 12 → NQ := ![l.q5,l.transfer_first,lift spend.DOMAIN_OWNER_KEY,lift spend.DOMAIN_NOTE,l.q15,lift spend.DOMAIN_NULLIFIER,l.q17,lift 8#u32,lift 18#u32,l.q19,lift 16#u32,l.q21]
def chunkLeft (l : Locals) : Fin 9 → NQ := ![l.q,l.q28,l.q30,l.q31,l.q33,l.q34,l.q36,l.chunk_eight,l.chunk_two]
def chunkRight (l : Locals) : Fin 9 → NQ := ![l.q1,l.q29,l.q3,l.q32,l.q5,l.q35,l.q37,l.private_chunk_eight,l.private_chunk_two]
def writeLeft (l : Locals) : Fin 4 → NQ := ![l.q9,l.q22,l.q9,l.q25]
def writeRight (l : Locals) : Fin 4 → NQ := ![l.domain,l.q23,l.length,l.q26]
def args (l : Locals) : Fin 5 → NQ := ![l.q38,l.fixed,l.chunk_two1,l.chunk_eight1,l.nodes]
structure Observations where
 prologue : Fin 12 → Event
 variant : pool_v1.pair_forest_semantic_terminal.CompiledVariant
 variantArgs : Fin 3 → NQ
 caches : Fin 2 → NP
 prologueResult : NQ × NQ × NQ × NQ × NQ × NQ × NP × NP
 constantResult : NQ × NQ
 chunkResult : NQ × NQ
 constants : Fin 12 → Event
 chunks : Fin 9 → Event
 laneCache : Fin 16 → NJB_PreparedCarrier.Index → NJB_PreparedCarrier.Index → U32
 laneOpened : Fin 16 → NQ
 laneReply : Fin 16 → NQ
 writes : Fin 4 → Event
 after : Array NQ 16#usize
 absorptionArgs : Fin 5 → NQ
 absorptionOpened : Array NQ 16#usize
 returned : Array NQ 16#usize × Array NQ 16#usize
 sumHigh : Fin 64 → NQ
 sumLow : Fin 16 → NQ
 ranges : Fin 4 → Nat
/-- Reviewed transcriptions of NJX initial prologue,12constants,9chunks,
16lane/from_fn,4write and final absorption-call windows, plus NKI_K009/010
receiver windows. Only asserted log/post/frame fields; field Result laws are
supplied separately at SAME arguments. Finite-index functions are the one
arbitrary-coordinate native record's occurrence projections. -/
def Cut (p : Public) (o : Openings) (s : Selectors) (l : Locals) (absorption : Array NQ 16#usize)
 (ob : Observations) (counts : Fin 7 → Nat) : Prop :=
 counts=![12,2,12,9,16,4,1] ∧
 (∀ j,(ob.prologue j).kind=proKind j ∧ (ob.prologue j).left=proLeft l j ∧ (ob.prologue j).right=proRight l j) ∧
 ob.variant=p.variant ∧ ob.variantArgs=![l.q6,l.q7,l.q8] ∧ ob.caches=![l.full,l.full_or_rate] ∧
 ob.prologueResult=(l.nodes,l.transfer_first,l.fixed,l.private_chunk_eight,l.private_chunk_two,l.full_initial_selector,l.full,l.full_or_rate) ∧
 ob.constantResult=(l.domain,l.length) ∧ ob.chunkResult=(l.chunk_eight1,l.chunk_two1) ∧
 (∀ j,(ob.constants j).kind=constantKind j ∧ (ob.constants j).left=constantLeft l j ∧ (ob.constants j).right=constantRight l j) ∧
 (∀ j,(ob.chunks j).kind=1 ∧ (ob.chunks j).left=chunkLeft l j ∧ (ob.chunks j).right=chunkRight l j) ∧
 (∀ i,ob.laneCache i=NJB_PreparedCarrier.words (if i.val<8 then l.full_or_rate else l.full) ∧
  ob.laneOpened i=NJB_ArrayCarrier.cell o.z i ∧ ob.laneReply i=NJB_ArrayCarrier.cell l.initial i) ∧
 (∀ j,(ob.writes j).left=writeLeft l j ∧ (ob.writes j).right=writeRight l j) ∧
 (∀ j,NJB_ArrayCarrier.cell ob.after j=if j.val=8 then l.q24 else if j.val=9 then l.q27 else NJB_ArrayCarrier.cell l.initial j) ∧
 ob.absorptionArgs=args l ∧ ob.absorptionOpened=o.z ∧ ob.returned=(l.initial2,absorption) ∧
 (∀ i,ob.sumHigh i=NJB_ArrayCarrier.cell s.high i) ∧
 (∀ i,ob.sumLow i=NJB_ArrayCarrier.cell s.low i) ∧ ob.ranges=![4,25,33,57]
def observations (p : Public) (o : Openings) (s : Selectors) (l : Locals) (absorption : Array NQ 16#usize) : Observations :=
 {prologue:=fun j=>⟨proKind j,proLeft l j,proRight l j⟩
  variant:=p.variant
  variantArgs:=![l.q6,l.q7,l.q8]
  caches:=![l.full,l.full_or_rate]
  prologueResult:=(l.nodes,l.transfer_first,l.fixed,l.private_chunk_eight,l.private_chunk_two,l.full_initial_selector,l.full,l.full_or_rate)
  constantResult:=(l.domain,l.length)
  chunkResult:=(l.chunk_eight1,l.chunk_two1)
  constants:=fun j=>⟨constantKind j,constantLeft l j,constantRight l j⟩
  chunks:=fun j=>⟨1,chunkLeft l j,chunkRight l j⟩
  laneCache:=fun i=>NJB_PreparedCarrier.words (if i.val<8 then l.full_or_rate else l.full)
  laneOpened:=NJB_ArrayCarrier.cell o.z
  laneReply:=NJB_ArrayCarrier.cell l.initial
  writes:=fun j=>⟨if j.val%2=0 then 0 else 2,writeLeft l j,writeRight l j⟩
  after:=l.initial2
  absorptionArgs:=args l
  absorptionOpened:=o.z
  returned:=(l.initial2,absorption)
  sumHigh:=NJB_ArrayCarrier.cell s.high
  sumLow:=NJB_ArrayCarrier.cell s.low
  ranges:=![4,25,33,57]}

theorem source (p : Public) (o : Openings) (s : Selectors) (l : Locals) (absorption : Array NQ 16#usize)
 (calls : NKI_InitialInvocation.Clauses p o s l) :
 Cut p o s l absorption (observations p o s l absorption) ![12,2,12,9,16,4,1] := by
 exact ⟨rfl,fun _=>⟨rfl,rfl,rfl⟩,rfl,rfl,rfl,rfl,rfl,rfl,fun _=>⟨rfl,rfl,rfl⟩,fun _=>⟨rfl,rfl,rfl⟩,
  fun _=>⟨rfl,rfl,rfl⟩,fun _=>⟨rfl,rfl⟩,NKI_InitialFrames.source p o s l calls,rfl,rfl,rfl,fun _=>rfl,fun _=>rfl,rfl⟩
#print Cut
#print axioms source
end AspisR1.NKI_InitialCuts
end
