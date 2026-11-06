import NKR_TermSemanticSource
import NKI_ArrayFrame
import NKI_ArrayCanonicalEq
import NKR_DigestAdd
set_option autoImplicit false
noncomputable section
namespace AspisR1.NKR_TermSemanticCut
open Aeneas Aeneas.Std Result FIq_Native
open FIv_NativeArithmetic (NQ)
open FIv_NativeValue (Canon decode)
open FIw_ArrayValue (canonical decoded)
open NKI_InitialPrefix (Public Openings Selectors)
open NKR_TermSemanticSource (Packed)
open pool_v1.pair_forest_semantic_terminal
abbrev Pair := Fin 2 → NQ
def rows : Fin 4 → Nat := ![232,229,233,228]
def pubArg (pub : Public) (i : Fin 4) : Option Public := if i.val=0 ∨ i.val=3 then some pub else none
structure Observation where
 publicArg : Option Public
 openingsArg : Openings
 selectorsArg : Selectors
 before : Packed
 after : Packed
 calls : Nat
 row : Nat
/-- NKR_semantic_child_cut on one arbitrary native prestate. All payload
coordinates are observed as values, no address-implies-payload premise. The
child may modify the complete24cell array. See native TRANSCRIPTION pins. -/
def Cut (pub : Public) (o : Openings) (s : Selectors) (i : Fin 4)
 (before reply : Packed) (ob : Observation) : Prop :=
 ob.publicArg=pubArg pub i ∧ ob.openingsArg=o ∧ ob.selectorsArg=s ∧
 ob.before=before ∧ ob.after=reply ∧ ob.calls=1 ∧ ob.row=rows i

def observation (pub : Public) (o : Openings) (s : Selectors) (i : Fin 4) (before reply : Packed) : Observation :=
 ⟨pubArg pub i,o,s,before,reply,1,rows i⟩

theorem cut_source (pub : Public) (o : Openings) (s : Selectors) (i : Fin 4) (before reply : Packed) :
 Cut pub o s i before reply (observation pub o s i before reply) := ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

def call (pub : Public) (o : Openings) (s : Selectors) : Fin 4 → Packed → Result Packed :=
 ![(fun before=>add_schedule_lanes before pub o s),(fun before=>add_path_lanes before o s),
   (fun before=>add_value_lanes before o s),(fun before=>add_occupancy_lanes before pub o s)]
inductive Trace (pub : Public) (o : Openings) (s : Selectors) : List (Fin 4) → Packed → Packed → Prop
 | nil (before) : Trace pub o s [] before before
 | cons {i is before middle after} : call pub o s i before=ok middle →
   Cut pub o s i before middle (observation pub o s i before middle) →
   Trace pub o s is middle after → Trace pub o s (i::is) before after
/-- The four native arbitrary-prestate windows chain through all24 cells on
one actual emitted invocation.232/233 candidates remain conditional on next
ledger adoption. CLOSED229/228 are used at SAME arrays/public/openings. -/
theorem prefix_source (pub : Public) (o : Openings) (s : Selectors)
 (p : NKR_TermSemanticSource.Packet pub o s) :
 Trace pub o s (List.finRange 4) NKR_TermSemanticSource.zero p.occupancy := by
 change Trace pub o s [0,1,2,3] NKR_TermSemanticSource.zero p.occupancy
 exact .cons p.schedule_call (cut_source pub o s 0 _ _)
  (.cons p.path_call (cut_source pub o s 1 _ _)
   (.cons p.value_call (cut_source pub o s 2 _ _)
    (.cons p.occupancy_call (cut_source pub o s 3 _ _) (.nil _))))

theorem zero (i : Fin (24#usize).val) :
 NJB_ArrayCarrier.cell NKR_TermSemanticSource.zero i=field.QM31.ZERO := by
 exact List.eq_of_mem_replicate (List.getElem_mem _)

/-- Native digest250 window's exact two scalar additions and full24frame. -/
def digestFrame (before : Packed) (replies : Pair) : Fin (24#usize).val → NQ :=
 fun j=>if j.val=21 then replies 0 else if j.val=22 then replies 1 else NJB_ArrayCarrier.cell before j

def digest_reference (before : Packed) (digests : Pair) : Result Packed := do
 let a←field.QM31.add (NJB_ArrayCarrier.cell before ⟨21,by decide⟩) (digests 0)
 let b←field.QM31.add (NJB_ArrayCarrier.cell before ⟨22,by decide⟩) (digests 1)
 ok (NJB_ArrayCarrier.array (digestFrame before ![a,b]))

structure DigestObservation where
 publicArg : Public
 openingsArg : Openings
 selectorsArg : Selectors
 addLeft : Pair
 addRight : Pair
 after : Packed
 calls : Nat

def DigestCut (pub : Public) (o : Openings) (s : Selectors) (before : Packed)
 (digests replies : Pair) (ob : DigestObservation) : Prop :=
 ob.publicArg=pub ∧ ob.openingsArg=o ∧ ob.selectorsArg=s ∧ ob.calls=3 ∧
 ob.addLeft=![NJB_ArrayCarrier.cell before ⟨21,by decide⟩,NJB_ArrayCarrier.cell before ⟨22,by decide⟩] ∧
 ob.addRight=digests ∧ ∀ j,NJB_ArrayCarrier.cell ob.after j=digestFrame before replies j

def digestObservation (pub : Public) (o : Openings) (s : Selectors) (before after : Packed) (digests : Pair) : DigestObservation :=
 ⟨pub,o,s,![NJB_ArrayCarrier.cell before ⟨21,by decide⟩,NJB_ArrayCarrier.cell before ⟨22,by decide⟩],digests,after,3⟩

theorem digest_source (pub : Public) (o : Openings) (s : Selectors) (before : Packed) (digests : Pair)
 (hb : canonical before) (hd : ∀ j,Canon (digests j)) :
 ∃ replies out,digest_reference before digests=ok out ∧ canonical out ∧
 (∀ g,field.QM31.add (NJB_ArrayCarrier.cell before (if g.val=0 then ⟨21,by decide⟩ else ⟨22,by decide⟩)) (digests g)=ok (replies g)) ∧
 DigestCut pub o s before digests replies (digestObservation pub o s before out digests) ∧
 ∀ g,decode (replies g)=decode (NJB_ArrayCarrier.cell before (if g.val=0 then ⟨21,by decide⟩ else ⟨22,by decide⟩))+decode (digests g) := by
 let slots : Fin 2 → Fin (24#usize).val := ![⟨21,by decide⟩,⟨22,by decide⟩]
 choose replies calls cr value using (fun g : Fin 2=>NJB_StubLaws.qm_add (NJB_ArrayCarrier.cell before (slots g)) (digests g) (NJB_ArrayCarrier.canonical_cell before hb _) (hd g))
 let out:=NJB_ArrayCarrier.array (digestFrame before replies)
 have vector : (![replies 0,replies 1] : Pair)=replies := by funext g;fin_cases g <;> rfl
 have co : canonical out := NJB_ArrayCarrier.canonical_array _ (fun j=>by
  unfold digestFrame
  split
  · exact cr 0
  · split
    · exact cr 1
    · exact NJB_ArrayCarrier.canonical_cell before hb j)
 refine ⟨replies,out,?_,co,?_,?_,?_⟩
 · simp only [digest_reference,calls,bind_tc_ok,vector]
   rfl
 · intro g;fin_cases g <;> exact calls _
 · exact ⟨rfl,rfl,rfl,rfl,rfl,rfl,fun j=>congrFun (NJB_ArrayCarrier.cell_array (digestFrame before replies)) j⟩
 · intro g;fin_cases g <;> exact value _
#print axioms cut_source
#print axioms prefix_source
#print axioms zero
#print axioms digest_source
end AspisR1.NKR_TermSemanticCut
end
