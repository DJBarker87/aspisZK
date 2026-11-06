import NKQ_ArrayWindows
set_option autoImplicit false
namespace AspisR1.NKQ_MaskCuts
open Aeneas Aeneas.Std Result AspisR1PublicPreparation NKQ_ArrayWindows
abbrev Q := aspis_core.field.QM31
abbrev Claims := Array (Array Q 29#usize) 3#usize
abbrev Alpha := Array Q 10#usize
def Canon (x : Q) : Prop := x.c0.a.val<2147483647 ∧ x.c0.b.val<2147483647 ∧ x.c1.a.val<2147483647 ∧ x.c1.b.val<2147483647
def CanonClaims (c : Claims) : Prop := ∀ row∈c.val,∀ x∈row.val,Canon x
def CanonAlpha (a : Alpha) : Prop := ∀ x∈a.val,Canon x
structure Post where
 low : Q
 high : Q
 blind : Q
 alpha : Q
 result : Q
 oracleReply : Q
 cellIndex : Nat
 calls : Nat
 claimsAfter : Claims
 alphaAfter : Alpha
abbrev Native := Claims → Alpha → Nat → Q → Post

def low (c : Claims) (i : Nat) (h : i<16) : Q := cell (cell c 0 (by decide)) i (by change i<29;omega)
def high (c : Claims) (i : Nat) : Q := cell (cell c 0 (by decide)) (16+i%10) (by change 16+i%10<29;have b:=Nat.mod_lt i (by decide : 0<10);omega)
def blind (c : Claims) : Q := cell (cell c 0 (by decide)) 27 (by decide)
def alpha (a : Alpha) (i : Nat) : Q := cell a (i%10) (by exact Nat.mod_lt i (by decide))

/-- Harness `crates/aspis-r1-cost-probe/src/NKQ_windows.rs`, SHA256 f6d51c1da0b0576e3592d7b7f73d3c2332809483d6a21f62589a814334a6216f.
NKQ_K043/K044, NKQ_windows.rs mask_low_cut/control. The only asserted
post fields are calls==1, out==log.reply and log.low==claims[0][i]. -/
def LowCut (native : Native) : Prop := ∀ c a i reply,CanonClaims c → CanonAlpha a → Canon reply → ∀ h:i<16,
 let p:=native c a i reply
 p.calls=1 ∧ p.result=reply ∧ p.low=low c i h
/-- Harness `crates/aspis-r1-cost-probe/src/NKQ_windows.rs`, SHA256 f6d51c1da0b0576e3592d7b7f73d3c2332809483d6a21f62589a814334a6216f.
NKQ_K045/K046: the SAME domain and exactly the high window assertion. -/
def HighCut (native : Native) : Prop := ∀ c a i reply,CanonClaims c → CanonAlpha a → Canon reply → i<16 →
 let p:=native c a i reply
 p.calls=1 ∧ p.result=reply ∧ p.high=high c i
/-- Harness `crates/aspis-r1-cost-probe/src/NKQ_windows.rs`, SHA256 f6d51c1da0b0576e3592d7b7f73d3c2332809483d6a21f62589a814334a6216f.
NKQ_K047/K048: the SAME domain and exactly claims[0][27]. -/
def BlindCut (native : Native) : Prop := ∀ c a i reply,CanonClaims c → CanonAlpha a → Canon reply → i<16 →
 let p:=native c a i reply
 p.calls=1 ∧ p.result=reply ∧ p.blind=blind c
/-- Harness `crates/aspis-r1-cost-probe/src/NKQ_windows.rs`, SHA256 f6d51c1da0b0576e3592d7b7f73d3c2332809483d6a21f62589a814334a6216f.
NKQ_K049/K050: observed alpha argument, not a reply coupled to alpha. -/
def AlphaCut (native : Native) : Prop := ∀ c a i reply,CanonClaims c → CanonAlpha a → Canon reply → i<16 →
 let p:=native c a i reply
 p.calls=1 ∧ p.result=reply ∧ p.alpha=alpha a i
/-- Harness `crates/aspis-r1-cost-probe/src/NKQ_windows.rs`, SHA256 f6d51c1da0b0576e3592d7b7f73d3c2332809483d6a21f62589a814334a6216f.
NKQ_K028/K029: arbitrary row/column and alpha index; caller values and
both non-modified log fields, plus returned reply. No child value law added. -/
def FrameCut (native : Native) : Prop := ∀ c a i reply,CanonClaims c → CanonAlpha a → Canon reply → i<16 →
 ∀ row (hr:row<3) col (hc:col<29) ai (ha:ai<10),
 let p:=native c a i reply
 cell (cell p.claimsAfter row hr) col hc=cell (cell c row hr) col hc ∧
 cell p.alphaAfter ai ha=cell a ai ha ∧ p.cellIndex=i ∧ p.oracleReply=reply ∧ p.result=reply

/-- Pointwise native observations compose by two array extensionality steps.
Every mode is instantiated on SAME arguments and an independent reply. This
is a mask-call component; no finish/terminal/native row root is concluded. -/
theorem arguments (native : Native) (lo : LowCut native) (hi : HighCut native)
 (bl : BlindCut native) (al : AlphaCut native) (fr : FrameCut native)
 (c : Claims) (a : Alpha) (i : Nat) (reply : Q)
 (cc : CanonClaims c) (ca : CanonAlpha a) (cr : Canon reply) (inside : i<16) :
 let p:=native c a i reply
 p.calls=1 ∧ p.result=reply ∧ p.low=low c i inside ∧ p.high=high c i ∧
 p.blind=blind c ∧ p.alpha=alpha a i ∧ p.claimsAfter=c ∧ p.alphaAfter=a := by
 have l:=lo c a i reply cc ca cr inside
 have h:=hi c a i reply cc ca cr inside
 have b:=bl c a i reply cc ca cr inside
 have v:=al c a i reply cc ca cr inside
 have claims : (native c a i reply).claimsAfter=c := by
  apply extensional
  intro row hr
  apply extensional
  intro col hc
  exact (fr c a i reply cc ca cr inside row hr col hc 0 (by decide)).1
 have alph : (native c a i reply).alphaAfter=a := by
  apply extensional
  intro index bound
  exact (fr c a i reply cc ca cr inside 0 (by decide) 0 (by decide) index bound).2.1
 exact ⟨l.1,l.2.1,l.2.2,h.2.2,b.2.2,v.2.2,claims,alph⟩
#print axioms arguments
#print arguments
end AspisR1.NKQ_MaskCuts
