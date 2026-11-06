from pathlib import Path
E=Path(__file__).resolve().parent
ops=[('sub','chi','v.v0'),('sub','chi','v.v1'),('sub','chi','v.v4'),('sub','chi','v.v5'),('mul','r.q0','r.q1'),('mul','r.q2','r.q3'),('mul','v.v2','r.q1'),('mul','v.v3','r.q0'),('add','r.q6','r.q7'),('mul','v.v6','r.q3'),('mul','v.v7','r.q2'),('add','r.q9','r.q10'),('mul','helper','r.q5'),('add','r.q12','r.q11'),('mul','r.q4','r.q13'),('mul','r.q5','r.q8'),('sub','r.q14','r.q15')]
reads=[('producer_values',0),('producer_values',1),('producer_weights',0),('producer_weights',1),('consumer_values',0),('consumer_values',1),('consumer_weights',0),('consumer_weights',1)]
s='''import NIH_COMBINED_IMPORT
import RPv_JFy_CopyResidual
import NDO_JFy_CopyResidualValue
set_option autoImplicit false
noncomputable section
namespace AspisR1.NIX_ResidualLog
open Aeneas Aeneas.Std Result FIq_Native
open pool_v1.pair_forest_copy_terminal
open FIv_NativeValue (Canon)
abbrev Q := field.QM31
structure Inputs where
'''+''.join(f' v{i} : Q\n' for i in range(8))+'structure Replies where\n'+''.join(f' q{i} : Q\n' for i in range(17))+'\ndef Reads (row : CopyRowExtension) (v : Inputs) : Prop :=\n '+' ∧\n '.join(f'row.{a}.index_usize {b}#usize=ok v.v{i}' for i,(a,b) in enumerate(reads))+'\n\ndef Law (v : Inputs) (helper chi : Q) (r : Replies) : Prop :=\n '+' ∧\n '.join(f'field.QM31.{op} {a} {b}=ok r.q{i}' for i,(op,a,b) in enumerate(ops))+'\n\ndef Domain (v : Inputs) (helper chi : Q) (r : Replies) : Prop :=\n '+' ∧ '.join(['Canon helper','Canon chi']+[f'Canon v.v{i}' for i in range(8)]+[f'Canon r.q{i}' for i in range(17)])+'\n\n'
s+='''theorem array0 (a b c d : Q) :
 (Array.make 4#usize [a,b,c,d]).index_usize 0#usize=ok a := by rfl
 theorem array1 (a b c d : Q) :
 (Array.make 4#usize [a,b,c,d]).index_usize 1#usize=ok b := by rfl
 theorem array2 (a b c d : Q) :
 (Array.make 4#usize [a,b,c,d]).index_usize 2#usize=ok c := by rfl
 theorem array3 (a b c d : Q) :
 (Array.make 4#usize [a,b,c,d]).index_usize 3#usize=ok d := by rfl

theorem source_of_log (row : CopyRowExtension) (v : Inputs) (helper chi : Q) (r : Replies)
 (reads : Reads row v) (law : Law v helper chi r) :
 copy_residual row helper chi=ok r.q16 := by
 rcases reads with ⟨h0,h1,h2,h3,h4,h5,h6,h7⟩
 rcases law with ⟨c0,c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,c11,c12,c13,c14,c15,c16⟩
 simp only [copy_residual,h0,h1,h2,h3,h4,h5,h6,h7,c0,c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,c11,c12,c13,c14,c15,c16,array0,array1,array2,array3,bind_tc_ok]

/-- Every input and opaque reply domain is derived for the same source row.
No copy_residual output or caller success is assumed. -/
theorem packet (row : CopyRowExtension) (helper chi : Q)
 (hpv : FIw_ArrayValue.canonical row.producer_values)
 (hpw : FIw_ArrayValue.canonical row.producer_weights)
 (hcv : FIw_ArrayValue.canonical row.consumer_values)
 (hcw : FIw_ArrayValue.canonical row.consumer_weights)
 (hh : Canon helper) (hc : Canon chi) :
 ∃ v r, Reads row v ∧ Law v helper chi r ∧ Domain v helper chi r ∧
 copy_residual row helper chi=ok r.q16 := by
'''
for i,(a,b) in enumerate(reads):
 prop={'producer_values':'hpv','producer_weights':'hpw','consumer_values':'hcv','consumer_weights':'hcw'}[a]
 s+=f' obtain ⟨v{i},h{i},d{i}⟩:=JFy_ArrayTotal.read row.{a} {b}#usize (by decide) {prop}\n'
s+=' let v : Inputs:=⟨'+','.join(f'v{i}' for i in range(8))+'⟩\n'
for i,(op,a,b) in enumerate(ops):
 a=a.replace('v.v','v').replace('r.q','q');b=b.replace('v.v','v').replace('r.q','q')
 def canon(x):return {'chi':'hc','helper':'hh'}.get(x,'d'+x[1:] if x.startswith('v') else 'e'+x[1:])
 fn='FIv_PreparedTotal.add' if op=='add' else 'JFy_FieldTotal.'+op
 s+=f' obtain ⟨q{i},c{i},e{i},_⟩:={fn} {a} {b} {canon(a)} {canon(b)}\n'
s+=' let r : Replies:=⟨'+','.join(f'q{i}' for i in range(17))+'⟩\n'
s+=' have reads : Reads row v:=⟨'+','.join(f'h{i}' for i in range(8))+'⟩\n'
s+=' have law : Law v helper chi r:=⟨'+','.join(f'c{i}' for i in range(17))+'⟩\n'
s+=' exact ⟨v,r,reads,law,⟨hh,hc,'+','.join([f'd{i}' for i in range(8)]+[f'e{i}' for i in range(17)])+'⟩,source_of_log row v helper chi r reads law⟩\n'
s+='\n#print axioms array0\n#print axioms array1\n#print axioms array2\n#print axioms array3\n#print axioms source_of_log\n#print axioms packet\nend AspisR1.NIX_ResidualLog\nend\n'
(E/'NIX_ResidualLog.lean').write_text(s)
