import NKR_DigestChildren
import NKR_DigestAdd
set_option autoImplicit false
noncomputable section
namespace AspisR1.NKR_DigestPrefix
open Aeneas Aeneas.Std Result
open FIv_NativeArithmetic (NQ)
open FIv_NativeValue (Canon decode K)
open NKI_InitialPrefix (Public Openings Selectors)
open NKR_DigestChildren (Pair Four Children Clauses Canonical)

def first (l : Four) : Pair := ![l 0,l 1]
def last (l : Four) : Pair := ![l 2,l 3]
def zero : Pair := fun _=>FIq_Native.field.QM31.ZERO
abbrev Sums := Fin 3 → Pair

def run (p : Public) (o : Openings) (s : Selectors) : Result (Children × Sums) := do
 let a←NKR_DigestChildren.left s o 56 p.anchor
 let v1←NKR_DigestAdd.add zero a
 let n←NKR_DigestChildren.left s o 26 p.nullifier
 let v2←NKR_DigestAdd.add v1 n
 let r←NJX_RecipientRoot.reference p.recipient o.z (NKR_DigestChildren.high s 29)
 let v3←NKR_DigestAdd.add v2 r
 let d←NKR_DigestChildren.left s o 32 p.change
 let v4←NKR_DigestAdd.add v3 d
 let l←NKI_LevelsFrame.run p.transition.live_snapshot.next_pair_index
  p.transition.live_snapshot.frontier o.z s.high (List.finRange 20) NKI_LevelsRoot.zero
 let v0←NKR_DigestAdd.add zero (first l)
 let v12←NKR_DigestAdd.add zero (last l)
 let root←NKR_DigestChildren.left s o 53 p.transition.candidate_afterstate.next_root
 let v5←NKR_DigestAdd.add v4 root
 let carry←FIq_Native.pool_v1.pair_forest_semantic_terminal.bounded_append_carry p.transition.live_snapshot.next_pair_index
 let carried←NJX_CarryRoot.reference carry.val (NKI_PublicDomains.high s carry.val) o.z
  (NJX_AppendDomains.frontier p.transition.candidate_afterstate.next_frontier (NKI_PublicDomains.carryLevel carry.val))
 let v6←NKR_DigestAdd.add v5 carried
 ok (⟨a,n,r,d,l,root,carry,carried⟩,![v0,v6,v12])

/-- Full arithmetic frame relation; every addition is paired at the exact
previous poststate. Returned children are logs, not root hypotheses. -/
structure Frame (c : Children) (out : Sums) : Prop where
 values0 : ∀ j,decode (out 0 j)=decode (first c.levels j)
 values11 : ∀ j,decode (out 1 j)=
  decode (c.anchor j)+decode (c.nullifier j)+decode (c.recipient j)+
   decode (c.change j)+decode (c.nextRoot j)+decode (c.carried j)
 values12 : ∀ j,decode (out 2 j)=decode (last c.levels j)

/-- Exact optimized251 source-ordered prefix. This is an authored reference
composition, not yet the missing native parent cut or whole-old-cohort law. -/
theorem source (p : Public) (o : Openings) (s : Selectors)
 (hp : NKR_DigestChildren.Domain p) (ho : FIw_ArrayValue.canonical o.z)
 (hh : FIw_ArrayValue.canonical s.high) :
 ∃ c sums,run p o s=ok (c,sums) ∧ Clauses p o s c ∧ Canonical c ∧
 (∀ g j,Canon (sums g j)) ∧ Frame c sums := by
 obtain ⟨c,hc,hcan⟩ := NKR_DigestChildren.source p o s hp ho hh
 have clauses:=hc
 have canonical:=hcan
 obtain ⟨ac,am,nc,nm,rc,rm,dc,dm,lc,rootc,rootm,cc,cv,hcarry,cac,cam⟩ := hc
 obtain ⟨ha,hn,hr,hd,hl,hroot,hca⟩ := hcan
 have hz : ∀ j,Canon (zero j) := fun _=>FIv_NativeValue.zero.1
 obtain ⟨v1,vc1,h1,val1⟩ := NKR_DigestAdd.source zero c.anchor hz ha
 obtain ⟨v2,vc2,h2,val2⟩ := NKR_DigestAdd.source v1 c.nullifier h1 hn
 obtain ⟨v3,vc3,h3,val3⟩ := NKR_DigestAdd.source v2 c.recipient h2 hr
 obtain ⟨v4,vc4,h4,val4⟩ := NKR_DigestAdd.source v3 c.change h3 hd
 have hf : ∀ j,Canon (first c.levels j) := by intro j;fin_cases j <;> exact hl _
 have ht : ∀ j,Canon (last c.levels j) := by intro j;fin_cases j <;> exact hl _
 obtain ⟨v0,vc0,h0,val0⟩ := NKR_DigestAdd.source zero (first c.levels) hz hf
 obtain ⟨v12,vc12,h12,val12⟩ := NKR_DigestAdd.source zero (last c.levels) hz ht
 obtain ⟨v5,vc5,h5,val5⟩ := NKR_DigestAdd.source v4 c.nextRoot h4 hroot
 obtain ⟨v6,vc6,h6,val6⟩ := NKR_DigestAdd.source v5 c.carried h5 hca
 refine ⟨c,![v0,v6,v12],?_,clauses,canonical,?_,?_⟩
 · simpa only [run,ac,nc,rc,dc,lc,rootc,cc,cac,vc1,vc2,vc3,vc4,vc0,vc12,vc5,vc6,bind_tc_ok]
 · intro g j
   fin_cases g
   · exact h0 j
   · exact h6 j
   · exact h12 j
 · constructor
   · intro j
     change decode (v0 j)=_
     rw [val0]
     simp only [zero,FIv_NativeValue.zero.2,zero_add]
   · intro j
     change decode (v6 j)=_
     rw [val6,val5,val4,val3,val2,val1]
     simp only [zero,FIv_NativeValue.zero.2,zero_add]
   · intro j
     change decode (v12 j)=_
     rw [val12]
     simp only [zero,FIv_NativeValue.zero.2,zero_add]
#print source
#print axioms source
end AspisR1.NKR_DigestPrefix
end
