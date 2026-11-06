import NKA_QueryPairs
set_option autoImplicit false
noncomputable section
namespace AspisR1.NKA_OuterCut
open Aeneas Aeneas.Std Result NJT_QBase
abbrev Blocks := NGQ_SamplerDriver.Blocks
abbrev Out := NGQ_SamplerDriver.Out

structure Post where
 state : State
 selected : Bytes
 stop : Bool
 seenState : State
 seenBlock : Bytes
 calls : Nat

abbrev Native := State → Bytes → Bytes → Bytes → Bool → State → Post

/-- NKA_K004/K005: one source iteration at k<8. Full child modifies is all22
cells, len and draws; no native scalar/frame constraint narrows that reply.
All32 byte and22 word windows compose by extensionality. -/
def Cut (native : Native) : Prop :=
 ∀ (before : State) (block advance carried : Bytes) (stop : Bool) (after : State),
 let post:=native before block advance carried stop after
 post.state=after ∧ post.selected=(if stop then advance else carried) ∧
 post.stop=stop ∧ post.seenState=before ∧ post.seenBlock=block ∧ post.calls=1

def walk (word : NJT_QScan.Native) (outer : Native) (advances : Blocks)
 (carried : Bytes) : List (Bytes×Usize) → State → Result Out
 | [],s => NHB_OuterState.finishCurrent carried s
 | (block,index)::tail,s => do
  let advance ← Array.index_usize advances index
  let next:=NJT_QScan.run word (NJT_QBase.words block).val s
  let post:=outer s block advance carried (Query31ExplicitListLoop.optionStop next.2) next.1
  if post.stop then NHB_OuterState.finishCurrent post.selected post.state
  else walk word outer advances post.selected tail post.state

/-- Forward child instantiation and loop induction. SAME source bounds are
proved from default, not imposed on native post-state by an oracle seed. -/
theorem association (word : NJT_QScan.Native) (wordCut : NJT_QScan.Cut word)
 (outer : Native) (outerCut : Cut outer) (advances : Blocks) (carried : Bytes)
 (inputs : List (Bytes×Usize)) (indices : ∀ pair∈inputs,pair.2.val<8)
 (s : State) (domain : NJT_QDomains.Domain s) :
 walk word outer advances carried inputs s =
 NHB_OuterState.walk (NJT_QPairs.nativeScan word) advances carried inputs s := by
 induction inputs generalizing s carried with
 | nil => rfl
 | cons head tail ih =>
  have bound:=indices head (List.mem_cons_self ..)
  have tailBound : ∀ pair∈tail,pair.2.val<8 := fun pair member=>indices pair (List.mem_cons_of_mem head member)
  have read:=NGQ_SamplerArray8.read advances head.2 bound
  let advance:=advances.val[head.2.val]'(by have h:=advances.property;change advances.val.length=8 at h;omega)
  let next:=NJT_QScan.run word (NJT_QBase.words head.1).val s
  obtain ⟨state,selected,stop,seenState,seenBlock,calls⟩:=outerCut s head.1 advance carried
   (Query31ExplicitListLoop.optionStop next.2) next.1
  simp only [walk,read,bind_tc_ok,NHB_OuterState.walk,NJT_QPairs.nativeScan]
  dsimp! only
  rw [state,selected,stop]
  cases flag : Query31ExplicitListLoop.optionStop next.2 with
  | true => simp only [flag,if_true,read,bind_tc_ok]
  | false =>
   simp only [flag,Bool.false_eq_true,if_false]
   exact ih carried tailBound next.1 (NJT_QDomains.scan_preserved word wordCut head.1 s domain)

/-- Native parent stage cuts + CLOSED child scan/finish at SAME arguments.
Only reviewed cut observations occur as Prop inputs; no child success,
external Run, endpoint equation or arbitrary cohort dictionary. -/
theorem queries_from_pairs (word : NJT_QScan.Native) (wordCut : NJT_QScan.Cut word)
 (outer : Native) (outerCut : Cut outer) (blocks advances : Blocks) :
 AspisR1Query31Transcript.queries_from_pairs_with_scan NGQ_SamplerPacket.Scan
 NGQ_SamplerPacket.initial blocks advances =
 walk word outer advances
  (advances.val[7]'(by have h:=advances.property;change advances.val.length=8 at h;omega))
  (NKA_QueryPairs.inputs blocks) NGQ_SamplerPacket.initial := by
 exact (NKA_QueryPairs.queries_from_pairs word wordCut blocks advances).trans
  (association word wordCut outer outerCut advances _ _ (NKA_QueryPairs.indices blocks)
    _ NJT_QDomains.initial).symm

#print queries_from_pairs
#print axioms association
#print axioms queries_from_pairs
end AspisR1.NKA_OuterCut
end
