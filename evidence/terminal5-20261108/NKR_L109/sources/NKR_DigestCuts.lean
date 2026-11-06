import NKR_DigestPrefix
/-! Reviewed(ai)(5) transcription of NKR_Digest_native.rs.txt SHA256
42668f77057f6fc84b92b4dba60e78926219ad3085fc73376e2dd818a1666e11.
Prefix assertions: `assert_eq!(log.calls,12)`; child kind/high/opened/some/digest;
add left=previous add reply, right=child reply; `out[group][lane]` equals
`adds[6+lane]` only for group1 and zero otherwise; high/succ/xor frames.
Middle assertions: `assert_eq!(l.calls,12)`; exact append index/frontier/
opened/highs; next-root high53/digest; carry index and carry reply; optional
high33+min(carry,19)/next_frontier[min]; addition operands; return `adds[k]`.
Wrapper assertions: `assert_eq!(l.calls,1)`; every Public scalar and arbitrary
coordinate of public/transition/opening/selector arrays; `out=reply`.
No arithmetic-value, success, endpoint or additional frame is asserted here.
Association is P6/D188 option-A reclassification, never trust removal. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.NKR_DigestCuts
open Aeneas Aeneas.Std Result
open FIv_NativeArithmetic (NQ)
open FIv_NativeValue (Canon)
open NJX_DigestCohort (D O)
open NJX_AppendDomains (Frontier High)
open NKI_InitialPrefix (Public Openings Selectors)
open NKR_DigestChildren (Pair Children Clauses Canonical)
abbrev Sums := Fin 3 → Pair
abbrev PrefixFrames := Fin 4 → Pair
structure MiddleFrames where
 local0 : Pair
 local12 : Pair
 nextRoot : Pair
 carried : Pair

/-- Value carrier for the selected-coordinate fields observed by native
NKR_Digest_prefix_cut/middle_cut. Irrelevant fields of an event are NOT clauses
of the cut. Full arrays are the universal-coordinate aggregation of exactly
the asserted words, under the existing P6/D188 reviewed transcription. -/
structure Event where
 kind : Nat
 high : NQ
 left : NQ
 right : NQ
 opened : O
 digest : D
 present : Bool
 index : U64
 carry : Nat
 highs : High
 frontier : Frontier

def zero := NKR_DigestPrefix.zero
def child (c : Children) : Fin 4 → Pair := ![c.anchor,c.nullifier,c.recipient,c.change]
def before (v : PrefixFrames) (g : Fin 4) : Pair :=
 if h : g.val=0 then zero else v ⟨g.val-1,by have h':=g.isLt;omega⟩
def high (s : Selectors) : Fin 4 → NQ :=
 ![NKR_DigestChildren.high s 56,NKR_DigestChildren.high s 26,NKR_DigestChildren.high s 29,NKR_DigestChildren.high s 32]
def digests (p : Public) : Fin 4 → Option D := ![some p.anchor,some p.nullifier,p.recipient,some p.change]
def digest (d : Option D) : D := d.getD (Array.repeat 8#usize 0#u32)
def baseEvent (p : Public) (o : Openings) (s : Selectors) (kind : Nat) : Event :=
 ⟨kind,FIq_Native.field.QM31.ZERO,FIq_Native.field.QM31.ZERO,FIq_Native.field.QM31.ZERO,
 o.z,Array.repeat 8#usize 0#u32,false,0#u64,0,s.high,p.transition.live_snapshot.frontier⟩
def childEvent (p : Public) (o : Openings) (s : Selectors) (g : Fin 4) : Event :=
 {baseEvent p o s (if g.val=2 then 12 else 11) with high:=high s g,digest:=digest (digests p g),present:=(digests p g).isSome}
def addEvent (p : Public) (o : Openings) (s : Selectors) (a b : NQ) : Event :=
 {baseEvent p o s 1 with left:=a,right:=b}
def prefixEvents (p : Public) (o : Openings) (s : Selectors) (c : Children) (v : PrefixFrames) : Fin 12 → Event :=
 ![childEvent p o s 0,addEvent p o s (zero 0) (c.anchor 0),addEvent p o s (zero 1) (c.anchor 1),
 childEvent p o s 1,addEvent p o s (v 0 0) (c.nullifier 0),addEvent p o s (v 0 1) (c.nullifier 1),
 childEvent p o s 2,addEvent p o s (v 1 0) (c.recipient 0),addEvent p o s (v 1 1) (c.recipient 1),
 childEvent p o s 3,addEvent p o s (v 2 0) (c.change 0),addEvent p o s (v 2 1) (c.change 1)]

/-- Exact NKR_Digest_prefix_cut assertions:12calls, forwarded four full child
arguments, eight ordered addition operands, full3x2return and asserted high/
succ/xor frames. No successful output or arithmetic law is a cut clause. -/
def PrefixCut (p : Public) (o : Openings) (s : Selectors) (c : Children) (v : PrefixFrames)
 (out : Sums) (events : Fin 12 → Event) (calls : Nat) (afterHigh : High) (afterSucc afterXor : O) : Prop :=
 calls=12 ∧ afterHigh=s.high ∧ afterSucc=o.succ_z ∧ afterXor=o.xor12_z ∧
 (∀ g : Fin 4,(events ⟨3*g.val,by have h:=g.isLt;omega⟩).kind=(if g.val=2 then 12 else 11) ∧
  (events ⟨3*g.val,by have h:=g.isLt;omega⟩).high=high s g ∧
  (events ⟨3*g.val,by have h:=g.isLt;omega⟩).opened=o.z ∧
  (events ⟨3*g.val,by have h:=g.isLt;omega⟩).present=(digests p g).isSome ∧
  (events ⟨3*g.val,by have h:=g.isLt;omega⟩).digest=digest (digests p g)) ∧
 (∀ (g : Fin 4) (j : Fin 2),(events ⟨3*g.val+1+j.val,by have h:=g.isLt;have h':=j.isLt;omega⟩).kind=1 ∧
  (events ⟨3*g.val+1+j.val,by have h:=g.isLt;have h':=j.isLt;omega⟩).left=before v g j ∧
  (events ⟨3*g.val+1+j.val,by have h:=g.isLt;have h':=j.isLt;omega⟩).right=child c g j) ∧
 out=(![zero,v 3,zero] : Sums)

theorem prefix_cut (p : Public) (o : Openings) (s : Selectors) (c : Children) (v : PrefixFrames) :
 PrefixCut p o s c v ![zero,v 3,zero] (prefixEvents p o s c v) 12 s.high o.succ_z o.xor12_z := by
 refine ⟨rfl,rfl,rfl,rfl,?_,?_,rfl⟩
 · intro g;fin_cases g <;> exact ⟨rfl,rfl,rfl,rfl,rfl⟩
 · intro g j;fin_cases g <;> fin_cases j <;> exact ⟨rfl,rfl,rfl⟩

def middleEvents (p : Public) (o : Openings) (s : Selectors) (c : Children) (pre : Sums) (m : MiddleFrames) : Fin 12 → Event :=
 ![{baseEvent p o s 21 with index:=p.transition.live_snapshot.next_pair_index},
 addEvent p o s (pre 0 0) (c.levels 0),addEvent p o s (pre 0 1) (c.levels 1),
 addEvent p o s (pre 2 0) (c.levels 2),addEvent p o s (pre 2 1) (c.levels 3),
 {baseEvent p o s 11 with high:=NKR_DigestChildren.high s 53,digest:=p.transition.candidate_afterstate.next_root},
 addEvent p o s (pre 1 0) (c.nextRoot 0),addEvent p o s (pre 1 1) (c.nextRoot 1),
 {baseEvent p o s 22 with index:=p.transition.live_snapshot.next_pair_index},
 {baseEvent p o s 23 with carry:=c.carry.val,high:=NKI_PublicDomains.high s c.carry.val,
  digest:=NJX_AppendDomains.frontier p.transition.candidate_afterstate.next_frontier (NKI_PublicDomains.carryLevel c.carry.val)},
 addEvent p o s (m.nextRoot 0) (c.carried 0),addEvent p o s (m.nextRoot 1) (c.carried 1)]

/-- Exact NKR_Digest_middle_cut assertions at arbitrary full3x2prestate:
append arguments/full4reply channels, next-root and carry/min arguments,
eight ordered additions and the complete returned3x2state. -/
def MiddleCut (p : Public) (o : Openings) (s : Selectors) (c : Children) (pre : Sums) (m : MiddleFrames)
 (out : Sums) (events : Fin 12 → Event) (calls : Nat) : Prop :=
 calls=12 ∧
 (events 0).kind=21 ∧ (events 0).index=p.transition.live_snapshot.next_pair_index ∧
 (events 0).frontier=p.transition.live_snapshot.frontier ∧ (events 0).opened=o.z ∧ (events 0).highs=s.high ∧
 (events 5).kind=11 ∧ (events 5).high=NKR_DigestChildren.high s 53 ∧ (events 5).opened=o.z ∧
 (events 5).digest=p.transition.candidate_afterstate.next_root ∧
 (events 8).kind=22 ∧ (events 8).index=p.transition.live_snapshot.next_pair_index ∧
 (events 9).kind=23 ∧ (events 9).carry=c.carry.val ∧ (events 9).opened=o.z ∧
 (events 9).high=NKI_PublicDomains.high s c.carry.val ∧
 (events 9).digest=NJX_AppendDomains.frontier p.transition.candidate_afterstate.next_frontier (NKI_PublicDomains.carryLevel c.carry.val) ∧
 (∀ j : Fin 2,
  (events ⟨1+j.val,by have h:=j.isLt;omega⟩).kind=1 ∧
  (events ⟨1+j.val,by have h:=j.isLt;omega⟩).left=pre 0 j ∧
  (events ⟨1+j.val,by have h:=j.isLt;omega⟩).right=NKR_DigestPrefix.first c.levels j ∧
  (events ⟨3+j.val,by have h:=j.isLt;omega⟩).kind=1 ∧
  (events ⟨3+j.val,by have h:=j.isLt;omega⟩).left=pre 2 j ∧
  (events ⟨3+j.val,by have h:=j.isLt;omega⟩).right=NKR_DigestPrefix.last c.levels j ∧
  (events ⟨6+j.val,by have h:=j.isLt;omega⟩).kind=1 ∧
  (events ⟨6+j.val,by have h:=j.isLt;omega⟩).left=pre 1 j ∧
  (events ⟨6+j.val,by have h:=j.isLt;omega⟩).right=c.nextRoot j ∧
  (events ⟨10+j.val,by have h:=j.isLt;omega⟩).kind=1 ∧
  (events ⟨10+j.val,by have h:=j.isLt;omega⟩).left=m.nextRoot j ∧
  (events ⟨10+j.val,by have h:=j.isLt;omega⟩).right=c.carried j) ∧
 out=(![m.local0,m.carried,m.local12] : Sums)

theorem middle_cut (p : Public) (o : Openings) (s : Selectors) (c : Children) (pre : Sums) (m : MiddleFrames) :
 MiddleCut p o s c pre m ![m.local0,m.carried,m.local12] (middleEvents p o s c pre m) 12 := by
 refine ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,?_,rfl⟩
 intro j;fin_cases j <;> exact ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

/-- NKR_Digest_wrapper_cut: universal-coordinate public/transition/opening/
selector payload checks, one call, and both unchanged return cells. -/
def WrapperCut (p : Public) (o : Openings) (s : Selectors) (seenP : Public) (seenO : Openings)
 (seenS : Selectors) (reply out : Pair) (calls : Nat) : Prop :=
 calls=1 ∧ seenP=p ∧ seenO=o ∧ seenS=s ∧ out=reply

theorem wrapper_cut (p : Public) (o : Openings) (s : Selectors) (reply : Pair) :
 WrapperCut p o s p o s reply reply 1 := ⟨rfl,rfl,rfl,rfl,rfl⟩

#print axioms prefix_cut
#print axioms middle_cut
#print axioms wrapper_cut
end AspisR1.NKR_DigestCuts
end
