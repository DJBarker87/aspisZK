from pathlib import Path
import re,sys
L=Path('docs/research/v8-r0-zk-20261009/lean/R1Z');raw=(L/'PV_B2_C_RawWeights251Funs.lean').read_text();targets=['aspis_core.field.wide_exact.WideExact.add','aspis_core.field.wide_exact.mul_u','aspis_core.field.wide_exact.WideExact.mul'];out='import R1Z.PV_B2_C_251FieldTotal\nset_option autoImplicit false\n'
names=[]
for name in targets:
 start=raw.index('def '+name+'\n');end=raw.index('\n/--',start);s=raw[start:end].strip();head,body=s.split(':=',1);head=head.replace('Result aspis_core.field.wide_exact.WideExact','aspis_core.field.wide_exact.WideExact').replace('Result aspis_core.field.QM31','aspis_core.field.QM31');body=re.sub(r'^\s*do\n','\n',body);body=body.replace(' ← ',' := ');body=re.sub(r'(?m)^  ok (.*)$',r'  \1',body);val=head+':='+body
 # Field value calls are pure; retain only these names and the already generated wide values.
 val=val.replace('aspis_core.field.','PV_B2_C_251FieldValue.aspis_core.field.')
 # Types need the raw carrier rather than the pure namespace alias for WideExact.
 val=val.replace('PV_B2_C_251FieldValue.aspis_core.field.wide_exact.WideExact','PV_B2_251c1.aspis_core.field.wide_exact.WideExact')
 # Restore the current declaration name inside the value namespace.
 val=val.replace('def PV_B2_251c1.'+name,'def '+name).replace('def PV_B2_C_251FieldValue.'+name,'def '+name)
 # Previously pure wide methods belong to the wide-value namespace.
 for old in targets:
  val=val.replace('PV_B2_C_251FieldValue.'+old,'PV_B2_C_251WideValue.'+old).replace('PV_B2_251c1.'+old,'PV_B2_C_251WideValue.'+old)
 val=val.replace('def PV_B2_C_251WideValue.'+name,'def '+name)
 lemma=name.replace('aspis_core.field.wide_exact.','').replace('.','_');names.append(lemma)
 params='(self rhs : PV_B2_251c1.aspis_core.field.wide_exact.WideExact)' if name.endswith(('WideExact.add','WideExact.mul')) else ('(value : PV_B2_251c1.aspis_core.field.QM31)' if name.endswith('mul_u') else '(value : PV_B2_251c1.aspis_core.field.wide_exact.WideExact) (q : PV_B2_251c1.aspis_core.field.QM31)')
 args='self rhs' if name.endswith(('WideExact.add','WideExact.mul')) else ('value' if name.endswith('mul_u') else 'value q')
 out+='namespace PV_B2_C_251WideValue\nopen Aeneas Aeneas.Std PV_B2_251c1\n'+val+'\nend PV_B2_C_251WideValue\nnamespace PV_B2_C_251WideTotal\nopen Aeneas Aeneas.Std Result\n'
 out+=f'theorem {lemma} {params} :\n PV_B2_251c1.{name} {args} = ok (PV_B2_C_251WideValue.{name} {args}) := by\n unfold PV_B2_251c1.{name} PV_B2_C_251WideValue.{name}\n simp only [PV_B2_C_251FieldTotal.QM31_add,PV_B2_C_251FieldTotal.QM31_sub,PV_B2_C_251FieldTotal.QM31_mul,PV_B2_C_251FieldTotal.mul_by_r,bind_tc_ok'+('' if len(names)==1 else ','+','.join('PV_B2_C_251WideTotal.'+n for n in names[:-1]))+']\n'
 out+=f'#print axioms {lemma}\nend PV_B2_C_251WideTotal\n'
p=L/'PV_B2_C_251WideTotal.lean'
if '--check' in sys.argv:assert p.read_text()==out
else:p.write_text(out)
