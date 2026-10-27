"""Emit small native arithmetic certificates; --check validates exact generated sources.
No whole recurrence is reduced: each arithmetic leaf uses named word-formula
lemmas and each loop composes a symbolic Segment. Numeric alphas are inherited
SHA diagnostic values; oracle-to-alpha binding is explicitly a separate gate.
"""
from pathlib import Path
import json,sys
P=Path(__file__).resolve().parent;R=P.parents[1]
rows=json.loads((P/'JFr_coefficients.json').read_text());out={};prime=2147483647
Q=lambda x:'(q '+' '.join(str(a)+'#u32' for a in x)+')'
canon=lambda x:'by change ('+str(x[0])+' < 2147483647 ∧ '+str(x[1])+' < 2147483647) ∧ ('+str(x[2])+' < 2147483647 ∧ '+str(x[3])+' < 2147483647); omega'
add=lambda x,y:[(a+b)%prime for a,b in zip(x,y)]
def cmul(x,y):return [(x[0]*y[0]-x[1]*y[1])%prime,(x[0]*y[1]+x[1]*y[0])%prime]
def mul(x,y):
 a=cmul(x[:2],y[:2]);c=cmul(x[2:],y[2:]);d=cmul(add(x[:2],x[2:]),add(y[:2],y[2:]));return add(a,[(2*c[0]-c[1])%prime,(c[0]+2*c[1])%prime])+[(d[i]-a[i]-c[i])%prime for i in range(2)]
for row in rows:
 r=row['round'];m=f'JFr_Data{r:02}';cs=row['coefficients'];lines=['import JFr_WordArithmetic','set_option autoImplicit false',f'namespace AspisR1.{m}','open Aeneas Aeneas.Std Result JFr_WordArithmetic']
 lines += [f'def c{i:02} : Q := {Q(c)}' for i,c in enumerate(cs)]
 lines += ['def p : Array Q 28#usize := ⟨['+','.join(f'c{i:02}' for i in range(28))+'],by rfl⟩',f'def running : Q := {Q(row["running"])}',f'def output : Q := {Q(row["value"])}','def alpha : Array Q 10#usize := ⟨['+','.join(Q(v['alpha']) for v in rows)+'],by rfl⟩']
 lines += [f'theorem canonical{i:02} : Canon c{i:02} := {canon(c)}\n#print axioms canonical{i:02}' for i,c in enumerate(cs)]
 lines += [f'end AspisR1.{m}'];out[m]='\n'.join(lines)+'\n'
 m=f'JFr_Boundary{r:02}';lines=[f'import JFr_Data{r:02}','import JFr_IndexArithmetic','set_option autoImplicit false',f'namespace AspisR1.{m}',f'open Aeneas Aeneas.Std Result JFr_WordArithmetic JFr_Data{r:02}']
 acc=cs[0];accs=[acc]
 for i,c in enumerate(cs):
  nxt=add(acc,c)
  lines += [f'theorem add{i:02} : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add {Q(acc)} c{i:02}=ok {Q(nxt)} :=',f'  JFr_WordArithmetic.add _ _ _ ({canon(acc)}) canonical{i:02} (by rfl)',f'#print axioms add{i:02}'];acc=nxt;accs.append(acc)
 assert acc==row['running']
 lines += ['theorem trace : JFr_BoundaryTrace.Segment p 0#usize c00 28#usize running := by']
 for i in range(28):
  lines += [f'  refine .step (by change {i}<28; omega) (show Array.index_usize p {i}#usize=ok c{i:02} from rfl) add{i:02} (JFr_IndexArithmetic.add {i}#usize {i+1}#usize rfl) ?_']
 lines += ['  exact .refl _ _','theorem source : AspisR1SemanticCallExtraction.r1_semantic.semantic_boundary p=ok running := by','  have first : Array.index_usize p 0#usize=ok c00 := rfl','  simp only [AspisR1SemanticCallExtraction.r1_semantic.semantic_boundary,first,bind_tc_ok]','  exact JFr_BoundaryTrace.source trace (by change ¬28<28; omega)','#print axioms trace','#print axioms source',f'end AspisR1.{m}'];out[m]='\n'.join(lines)+'\n'
 # Two Horner segments, fourteen coefficients each; intermediate states are pinned.
 acc=[0]*4
 for half in range(2):
  start=28-half*14;stop=start-14;initial=acc
  m=f'JFr_Horner{r:02}_{half}';lines=[f'import JFr_Data{r:02}','import JFr_HornerTrace','set_option autoImplicit false',f'namespace AspisR1.{m}',f'open Aeneas Aeneas.Std Result JFr_WordArithmetic JFr_Data{r:02}']
  lines += [f'def initial : Q := {Q(initial)}']
  for i in reversed(range(stop,start)):
   prod=mul(acc,row['alpha']);nxt=add(prod,cs[i]);
   lines += [f'theorem mul{i:02} : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul {Q(acc)} {Q(row["alpha"])}=ok {Q(prod)} :=',f'  JFr_WordArithmetic.mul _ _ _ ({canon(acc)}) ({canon(row["alpha"])}) (by rfl)',f'#print axioms mul{i:02}',f'theorem add{i:02} : AspisR1SemanticCallExtraction.aspis_core.field.QM31.add {Q(prod)} c{i:02}=ok {Q(nxt)} :=',f'  JFr_WordArithmetic.add _ _ _ ({canon(prod)}) canonical{i:02} (by rfl)',f'#print axioms add{i:02}'];acc=nxt
  lines += [f'def final : Q := {Q(acc)}',f'theorem trace : JFr_HornerTrace.Segment p alpha {r}#usize {start}#usize initial {stop}#usize final := by']
  for i in reversed(range(stop,start)):
   lines += [f'  refine .step (by change {i+1}>0; omega) (JFr_IndexArithmetic.sub {i+1}#usize {i}#usize rfl) (show Array.index_usize alpha {r}#usize=ok {Q(row["alpha"])} from rfl) mul{i:02} (show Array.index_usize p {i}#usize=ok c{i:02} from rfl) add{i:02} ?_']
  lines += ['  exact .refl _ _','#print axioms trace',f'end AspisR1.{m}'];out[m]='\n'.join(lines)+'\n'
 assert acc==row['value']
for m,s in out.items():
 f=R/'lean'/(m+'.lean')
 if '--check' in sys.argv:assert f.read_text()==s,m
 else:f.write_text(s)
print(json.dumps(dict(modules=len(out),checked='--check' in sys.argv,sparse_shapes='No exceptional recurrence cells: 28 explicit nonzero coefficients; each primitive operation is a separate theorem; loop closure uses Segment.source; no recurrence reduction.')))
