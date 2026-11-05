import NIX_ResidualLog
set_option autoImplicit false
noncomputable section
namespace AspisR1.NIX_ResidualCut
open Aeneas Aeneas.Std Result FIq_Native
open pool_v1.pair_forest_copy_terminal
open NIX_ResidualLog
structure Post where
 args : Fin 17 → Q × Q
 kind : Fin 17 → Nat
 at : Fin 17 → Nat
 count : Nat
 frame : Nat
 result : Q

def operands (v : Inputs) (helper chi : Q) (r : Replies) (i : Fin 17) : Q × Q :=
 match i.val with
 | 0=>(chi,v.v0)
 | 1=>(chi,v.v1)
 | 2=>(chi,v.v4)
 | 3=>(chi,v.v5)
 | 4=>(r.q0,r.q1)
 | 5=>(r.q2,r.q3)
 | 6=>(v.v2,r.q1)
 | 7=>(v.v3,r.q0)
 | 8=>(r.q6,r.q7)
 | 9=>(v.v6,r.q3)
 | 10=>(v.v7,r.q2)
 | 11=>(r.q9,r.q10)
 | 12=>(helper,r.q5)
 | 13=>(r.q12,r.q11)
 | 14=>(r.q4,r.q13)
 | 15=>(r.q5,r.q8)
 | _=>(r.q14,r.q15)
def kind (i : Fin 17) : Nat :=
 match i.val with
 | 0=>0
 | 1=>0
 | 2=>0
 | 3=>0
 | 4=>1
 | 5=>1
 | 6=>1
 | 7=>1
 | 8=>2
 | 9=>1
 | 10=>1
 | 11=>2
 | 12=>1
 | 13=>2
 | 14=>1
 | 15=>1
 | _=>0

/-- NIX_residual.rs.txt SHA256 1c678ac5885301b020ca62c86037621d9fc99c8667670bc68d7e0dbc2e4da0f2, K058/K059.
Exact assumptions: canonical row/helper/chi and all 17 opaque replies, count<239.
Exact assertions for arbitrary i<17: same(args[2*i],expected[i].0) and
same(args[2*i+1],expected[i].1); canonical(both); kind[i]==kinds[i];
at[i]==count+i; count==old+17; frame==old; same(result,o[16]).
No field equation or output/source equality is inserted into this native cut. -/
def cut (v : Inputs) (helper chi : Q) (r : Replies) (count frame : Nat) (p : Post) : Prop :=
 Domain v helper chi r ∧ count<239 ∧
 (∀ i,p.args i=operands v helper chi r i ∧
  FIv_NativeValue.Canon (p.args i).1 ∧ FIv_NativeValue.Canon (p.args i).2 ∧
  p.kind i=kind i ∧ p.at i=count+i.val) ∧
 p.count=count+17 ∧ p.frame=frame ∧ p.result=r.q16

theorem source (row : CopyRowExtension) (v : Inputs) (helper chi : Q) (r : Replies)
 (count frame : Nat) (p : Post) (reads : Reads row v) (law : Law v helper chi r)
 (certificate : cut v helper chi r count frame p) :
 copy_residual row helper chi=ok p.result := by
 rw [certificate.2.2.2.2.2]
 exact NIX_ResidualLog.source_of_log row v helper chi r reads law

/-- Canonical SAME-row domains derive all 17 callee replies and the endpoint
meaning. Neither caller success nor an arbitrarily chosen output is assumed. -/
theorem packet (row : CopyRowExtension) (helper chi : Q)
 (hpv : FIw_ArrayValue.canonical row.producer_values)
 (hpw : FIw_ArrayValue.canonical row.producer_weights)
 (hcv : FIw_ArrayValue.canonical row.consumer_values)
 (hcw : FIw_ArrayValue.canonical row.consumer_weights)
 (hh : FIv_NativeValue.Canon helper) (hc : FIv_NativeValue.Canon chi) :
 ∃ v r,Reads row v ∧ Law v helper chi r ∧ Domain v helper chi r ∧
 ∀ count frame p,cut v helper chi r count frame p →
 copy_residual row helper chi=ok p.result ∧ FIv_NativeValue.Canon p.result ∧
 FIv_NativeValue.decode p.result=FIw_CopyMeaning.residual row
  (FIv_NativeValue.decode helper) (FIv_NativeValue.decode chi) := by
 obtain ⟨v,r,reads,law,domain,_⟩:=NIX_ResidualLog.packet row helper chi hpv hpw hcv hcw hh hc
 refine ⟨v,r,reads,law,domain,?_⟩
 intro count frame p certificate
 have run:=source row v helper chi r count frame p reads law certificate
 exact ⟨run,FIw_CopyMeaning.value_exact row helper chi p.result hpv hcv hpw hcw hh hc run⟩

#print axioms source
#print axioms packet
end AspisR1.NIX_ResidualCut
end
