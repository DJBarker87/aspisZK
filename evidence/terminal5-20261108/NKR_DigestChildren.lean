import NKR_DigestCarry
import NKI_LevelsComplete
import NKI_PublicDomains
import NJX_LeftCutRoot
import NJX_CarryRoot
import NJX_RecipientRoot
import NKI_InitialPrefix
set_option autoImplicit false
noncomputable section
namespace AspisR1.NKR_DigestChildren
open Aeneas Aeneas.Std Result
open FIv_NativeArithmetic (NQ)
open FIv_NativeValue (Canon)
open NJX_DigestCohort (D O dc ocells dcells)
open NKI_InitialPrefix (Public Openings Selectors)
abbrev Pair := Fin 2 → NQ
abbrev Four := Fin 4 → NQ

def high (s : Selectors) (i : Fin 64) : NQ :=
 NJB_ArrayCarrier.cell s.high ⟨i.val,by have h:=i.isLt;scalar_tac⟩

def left (s : Selectors) (o : Openings) (i : Fin 64) (d : D) : Result Pair :=
 NJX_DigestPacket.reference (high s i) (ocells o.z) (dcells d)

/-- All digest domains are actual fields read by251. No source/frontier,
recipient or carry-index domain is silently supplied by a child hypothesis. -/
structure Domain (p : Public) : Prop where
 anchor : dc p.anchor
 nullifier : dc p.nullifier
 recipient : ∀ d,p.recipient=some d→dc d
 change : dc p.change
 frontier : ∀ d∈p.transition.live_snapshot.frontier.val,dc d
 nextRoot : dc p.transition.candidate_afterstate.next_root
 nextFrontier : ∀ d∈p.transition.candidate_afterstate.next_frontier.val,dc d

structure Children where
 anchor : Pair
 nullifier : Pair
 recipient : Pair
 change : Pair
 levels : Four
 nextRoot : Pair
 carry : Usize
 carried : Pair

def Canonical (c : Children) : Prop :=
 (∀ j,Canon (c.anchor j)) ∧ (∀ j,Canon (c.nullifier j)) ∧
 (∀ j,Canon (c.recipient j)) ∧ (∀ j,Canon (c.change j)) ∧
 (∀ j,Canon (c.levels j)) ∧ (∀ j,Canon (c.nextRoot j)) ∧
 (∀ j,Canon (c.carried j))

/-- Complete actual SAME-call child clauses of251 in source order.
NKI235/NJX242/245/246 credit remains conditional on next ledger adoption. -/
def Clauses (p : Public) (o : Openings) (s : Selectors) (c : Children) : Prop :=
 left s o 56 p.anchor=ok c.anchor ∧
 NJX_LeftRoot.cohort (high s 56) o.z p.anchor=ok c.anchor ∧
 left s o 26 p.nullifier=ok c.nullifier ∧
 NJX_LeftRoot.cohort (high s 26) o.z p.nullifier=ok c.nullifier ∧
 NJX_RecipientRoot.reference p.recipient o.z (high s 29)=ok c.recipient ∧
 NJX_RecipientRoot.cohort p.recipient o.z (high s 29)=ok c.recipient ∧
 left s o 32 p.change=ok c.change ∧
 NJX_LeftRoot.cohort (high s 32) o.z p.change=ok c.change ∧
 NKI_LevelsFrame.run p.transition.live_snapshot.next_pair_index
  p.transition.live_snapshot.frontier o.z s.high (List.finRange 20) NKI_LevelsRoot.zero=ok c.levels ∧
 left s o 53 p.transition.candidate_afterstate.next_root=ok c.nextRoot ∧
 NJX_LeftRoot.cohort (high s 53) o.z p.transition.candidate_afterstate.next_root=ok c.nextRoot ∧
 FIq_Native.pool_v1.pair_forest_semantic_terminal.bounded_append_carry
  p.transition.live_snapshot.next_pair_index=ok c.carry ∧
 c.carry.val=R0P.digestCarry p.transition.live_snapshot.next_pair_index.val ∧ c.carry.val≤20 ∧
 NJX_CarryRoot.reference c.carry.val (NKI_PublicDomains.high s c.carry.val) o.z
  (NJX_AppendDomains.frontier p.transition.candidate_afterstate.next_frontier (NKI_PublicDomains.carryLevel c.carry.val))=ok c.carried ∧
 NJX_CarryRoot.cohort c.carry.val (NKI_PublicDomains.high s c.carry.val) o.z
  (NJX_AppendDomains.frontier p.transition.candidate_afterstate.next_frontier (NKI_PublicDomains.carryLevel c.carry.val))=ok c.carried

/-- Every child result is derived internally at the exact caller arguments. -/
theorem source (p : Public) (o : Openings) (s : Selectors)
 (hp : Domain p) (ho : FIw_ArrayValue.canonical o.z) (hs : FIw_ArrayValue.canonical s.high) :
 ∃ c,Clauses p o s c ∧ Canonical c := by
 have hh : ∀ i,Canon (high s i) := fun i=>NJB_ArrayCarrier.canonical_cell s.high hs _
 obtain ⟨a,ac,am⟩ := NJX_LeftRoot.source (high s 56) o.z p.anchor (hh 56) ho hp.anchor
 obtain ⟨n,nc,nm⟩ := NJX_LeftRoot.source (high s 26) o.z p.nullifier (hh 26) ho hp.nullifier
 obtain ⟨r,cache,rc,rm,hr,_,_⟩ := NJX_RecipientRoot.source p.recipient o.z (high s 29) (hh 29) ho hp.recipient
 obtain ⟨d,dc',dm⟩ := NJX_LeftRoot.source (high s 32) o.z p.change (hh 32) ho hp.change
 obtain ⟨packets,levels,_,lc,_,hl,_⟩ := NKI_LevelsComplete.source
  p.transition.live_snapshot.next_pair_index p.transition.live_snapshot.frontier o.z s.high hp.frontier ho hs
 obtain ⟨root,rootc,rootm⟩ := NJX_LeftRoot.source (high s 53) o.z
  p.transition.candidate_afterstate.next_root (hh 53) ho hp.nextRoot
 obtain ⟨carry,cc,cv,hc⟩ := NKR_DigestCarry.source p.transition.live_snapshot.next_pair_index
 have ch : Canon (NKI_PublicDomains.high s carry.val) := NJB_ArrayCarrier.canonical_cell s.high hs _
 have cd : dc (NJX_AppendDomains.frontier p.transition.candidate_afterstate.next_frontier (NKI_PublicDomains.carryLevel carry.val)) :=
  hp.nextFrontier _ (List.getElem_mem _)
 obtain ⟨carried,cac,cam,hca,_⟩ := NJX_CarryRoot.source carry.val (NKI_PublicDomains.high s carry.val) o.z _ ch ho cd
 exact ⟨⟨a.out,n.out,r,d.out,levels,root.out,carry,carried⟩,
  ⟨ac,am,nc,nm,rc,rm,dc',dm,lc,rootc,rootm,cc,cv,hc,cac,cam⟩,
  a.out_canonical,n.out_canonical,hr,d.out_canonical,hl,root.out_canonical,hca⟩
#print source
#print axioms source
end AspisR1.NKR_DigestChildren
end
