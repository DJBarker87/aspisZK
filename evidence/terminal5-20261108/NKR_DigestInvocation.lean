import NKR_DigestCuts
set_option autoImplicit false
noncomputable section
namespace AspisR1.NKR_DigestInvocation
open Aeneas Aeneas.Std Result
open FIv_NativeValue (Canon)
open NKI_InitialPrefix (Public Openings Selectors)
open NKR_DigestChildren (Pair Children Clauses Canonical)
open NKR_DigestCuts (Sums PrefixFrames MiddleFrames zero child before)

def PrefixArithmetic (c : Children) (v : PrefixFrames) : Prop :=
 ∀ g,NKR_DigestAdd.add (before v g) (child c g)=ok (v g)
def MiddleArithmetic (c : Children) (pre : Sums) (m : MiddleFrames) : Prop :=
 NKR_DigestAdd.add (pre 0) (NKR_DigestPrefix.first c.levels)=ok m.local0 ∧
 NKR_DigestAdd.add (pre 2) (NKR_DigestPrefix.last c.levels)=ok m.local12 ∧
 NKR_DigestAdd.add (pre 1) c.nextRoot=ok m.nextRoot ∧
 NKR_DigestAdd.add m.nextRoot c.carried=ok m.carried

theorem prefix_source (c : Children) (hc : Canonical c) :
 ∃ v,PrefixArithmetic c v ∧ ∀ g j,Canon (v g j) := by
 obtain ⟨ha,hn,hr,hd,_,_,_⟩ := hc
 have hz : ∀ j,Canon (zero j) := fun _=>FIv_NativeValue.zero.1
 obtain ⟨v0,vc0,h0,_⟩ := NKR_DigestAdd.source zero c.anchor hz ha
 obtain ⟨v1,vc1,h1,_⟩ := NKR_DigestAdd.source v0 c.nullifier h0 hn
 obtain ⟨v2,vc2,h2,_⟩ := NKR_DigestAdd.source v1 c.recipient h1 hr
 obtain ⟨v3,vc3,h3,_⟩ := NKR_DigestAdd.source v2 c.change h2 hd
 refine ⟨![v0,v1,v2,v3],?_,?_⟩
 · intro g;fin_cases g <;> first | exact vc0 | exact vc1 | exact vc2 | exact vc3
 · intro g j;fin_cases g <;> first | exact h0 j | exact h1 j | exact h2 j | exact h3 j

theorem middle_source (c : Children) (pre : Sums) (hc : Canonical c)
 (hp : ∀ g j,Canon (pre g j)) :
 ∃ m,MiddleArithmetic c pre m ∧
 ∀ g j,Canon ((![m.local0,m.carried,m.local12] : Sums) g j) := by
 obtain ⟨_,_,_,_,hl,hr,hca⟩ := hc
 have hf : ∀ j,Canon (NKR_DigestPrefix.first c.levels j) := by intro j;fin_cases j <;> exact hl _
 have ht : ∀ j,Canon (NKR_DigestPrefix.last c.levels j) := by intro j;fin_cases j <;> exact hl _
 obtain ⟨v0,vc0,h0,_⟩ := NKR_DigestAdd.source (pre 0) (NKR_DigestPrefix.first c.levels) (hp 0) hf
 obtain ⟨v12,vc12,h12,_⟩ := NKR_DigestAdd.source (pre 2) (NKR_DigestPrefix.last c.levels) (hp 2) ht
 obtain ⟨vr,vcr,hr',_⟩ := NKR_DigestAdd.source (pre 1) c.nextRoot (hp 1) hr
 obtain ⟨vc,vcc,hc',_⟩ := NKR_DigestAdd.source vr c.carried hr' hca
 refine ⟨⟨v0,v12,vr,vc⟩,⟨vc0,vc12,vcr,vcc⟩,?_⟩
 intro g j;fin_cases g <;> first | exact h0 j | exact hc' j | exact h12 j

/-- Forward(aq)(5) association: instantiate universal native reply records
with these SAME actual child Results and field addition replies. The source
ordered body then gives the full post, without an inverse raw-log premise. -/
theorem association (p : Public) (o : Openings) (s : Selectors) (c : Children)
 (v : PrefixFrames) (m : MiddleFrames) (hc : Clauses p o s c)
 (hv : PrefixArithmetic c v) (hm : MiddleArithmetic c ![zero,v 3,zero] m) :
 NKR_DigestPrefix.run p o s=ok (c,![m.local0,m.carried,m.local12]) := by
 obtain ⟨ac,_,nc,_,rc,_,dc,_,lc,rootc,_,cc,_,_,cac,_⟩ := hc
 have vc0 : NKR_DigestAdd.add zero c.anchor=ok (v 0) := hv 0
 have vc1 : NKR_DigestAdd.add (v 0) c.nullifier=ok (v 1) := hv 1
 have vc2 : NKR_DigestAdd.add (v 1) c.recipient=ok (v 2) := hv 2
 have vc3 : NKR_DigestAdd.add (v 2) c.change=ok (v 3) := hv 3
 obtain ⟨mc0,mc12,mcr,mcc⟩ := hm
 simpa only [NKR_DigestPrefix.run,ac,nc,rc,dc,lc,rootc,cc,cac,vc0,vc1,vc2,vc3,mc0,mc12,mcr,mcc,bind_tc_ok]

/-- Native-prefix and native-middle cuts chained at the SAME full poststate,
with every arithmetic law/domain derived internally. -/
theorem source (p : Public) (o : Openings) (s : Selectors) (c : Children)
 (hc : Clauses p o s c) (hcan : Canonical c) :
 ∃ v m,PrefixArithmetic c v ∧ MiddleArithmetic c ![zero,v 3,zero] m ∧
 NKR_DigestCuts.PrefixCut p o s c v ![zero,v 3,zero] (NKR_DigestCuts.prefixEvents p o s c v) 12 s.high o.succ_z o.xor12_z ∧
 NKR_DigestCuts.MiddleCut p o s c ![zero,v 3,zero] m ![m.local0,m.carried,m.local12]
  (NKR_DigestCuts.middleEvents p o s c ![zero,v 3,zero] m) 12 ∧
 NKR_DigestPrefix.run p o s=ok (c,![m.local0,m.carried,m.local12]) ∧
 ∀ g j,Canon ((![m.local0,m.carried,m.local12] : Sums) g j) := by
 obtain ⟨v,vc,hv⟩ := prefix_source c hcan
 have pre : ∀ g j,Canon ((![zero,v 3,zero] : Sums) g j) := by
  intro g j;fin_cases g <;> first | exact FIv_NativeValue.zero.1 | exact hv 3 j
 obtain ⟨m,mc,hm⟩ := middle_source c ![zero,v 3,zero] hcan pre
 exact ⟨v,m,vc,mc,NKR_DigestCuts.prefix_cut p o s c v,
  NKR_DigestCuts.middle_cut p o s c ![zero,v 3,zero] m,association p o s c v m hc vc mc,hm⟩
#print axioms prefix_source
#print axioms middle_source
#print axioms association
#print axioms source
end AspisR1.NKR_DigestInvocation
end
