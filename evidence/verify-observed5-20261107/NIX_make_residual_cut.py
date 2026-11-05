from pathlib import Path
import hashlib
E=Path(__file__).resolve().parent;h=hashlib.sha256((E/'NIX_residual.rs.txt').read_bytes()).hexdigest()
ops=[('chi','v.v0',0),('chi','v.v1',0),('chi','v.v4',0),('chi','v.v5',0),('r.q0','r.q1',1),('r.q2','r.q3',1),('v.v2','r.q1',1),('v.v3','r.q0',1),('r.q6','r.q7',2),('v.v6','r.q3',1),('v.v7','r.q2',1),('r.q9','r.q10',2),('helper','r.q5',1),('r.q12','r.q11',2),('r.q4','r.q13',1),('r.q5','r.q8',1),('r.q14','r.q15',0)]
s='''import NIX_ResidualLog
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
'''+''.join(f' | {i}=>({a},{b})\n' for i,(a,b,k) in enumerate(ops[:-1]))+f' | _=>({ops[-1][0]},{ops[-1][1]})\n'
s+='def kind (i : Fin 17) : Nat :=\n match i.val with\n'+''.join(f' | {i}=>{k}\n' for i,(a,b,k) in enumerate(ops[:-1]))+f' | _=>{ops[-1][2]}\n'
s+='''
/-- NIX_residual.rs.txt SHA256 HASH, K058/K059.
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
'''.replace('HASH',h)
(E/'NIX_ResidualCut.lean').write_text(s)
