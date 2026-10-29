"""Apply the completed small model transformations at five actual callers."""
from pathlib import Path
import re,json,sys
D=Path('evidence/pv-b3p6-20261028');L=D/'lean';files={};rows=[]
raw=(D/'raw227-composition-resume5/Funs.lean').read_text()
h='namespace PV_B3P_Binding12227\nopen Aeneas Aeneas.Std PV_B3P_227 Result ControlFlow Error\nset_option autoImplicit false\n'
specs=[
 ('reference_poseidon.internal_round','reference_poseidon.internal_linear_lazy','Array aspis_core.field.QM31 16#usize → Result (Array aspis_core.field.QM31 16#usize)','source_internal12','(funext internal_linear_binding12)'),
 ('reference_copy_terminal.pattern_values','reference_copy_terminal.pattern_values_literal','Array aspis_core.field.QM31 16#usize → aspis_core.field.QM31 → Result (Array aspis_core.field.QM31 14#usize)','source_pattern_values12','(funext fun openings => funext fun lambda => pattern_values_literal_binding12 openings lambda)'),
 ('reference_copy_terminal.evaluate_with_selectors','reference_copy_terminal.Selectors.active','reference_copy_terminal.Selectors → Result aspis_core.field.QM31','source_active12','active_operation12'),
 ('reference_terminal.semantic_packed','reference_terminal.add_value_lanes','Array aspis_core.field.QM31 24#usize → aspis_statement.state_only_poseidon.StateOnlyPoseidonOpenings → reference_copy_terminal.Selectors → Result (Array aspis_core.field.QM31 24#usize)','value_source12','(funext fun packed => funext fun openings => funext fun selectors => value_caller_binding12 packed openings selectors)'),
 ('reference_poseidon.evaluate_state_only_poseidon_oracle_projected','reference_poseidon.leading_pair_packed','aspis_statement.state_only_poseidon.StateOnlyPoseidonOpenings → Result (Array aspis_core.field.QM31 4#usize)','source_leading12','leading_operation12')]
for i,(name,callee,ty,source,law) in enumerate(specs):
 if i==4:
  rows.append(dict(module='PV_B3P_ActualCaller124227',caller=name,callee=callee,theorem=None,credit='REJECTED whole-context congruence at default recursion depth; do not regenerate or retry',next='split selector prefix and four packed-group continuations into named opaque stages'))
  continue
 decl=re.search(r'^def '+re.escape(name)+r'\s*\n[\s\S]*?(?=^/--|\Z)',raw,re.M)[0].strip()
 head,body=decl.split(':=',1);params=head[head.index(name)+len(name):]
 depth=0;boundary=None
 for j,c in enumerate(params):
  if c in '([{':depth+=1
  elif c in ')]}':depth-=1
  elif c==':' and depth==0:boundary=j;break
 pars=params[:boundary];args=[];depth=0;start=0
 for j,c in enumerate(pars):
  if c in '({':
   if depth==0:start=j+1
   depth+=1
  elif c in ')}':
   depth-=1
   if depth==0:args+=pars[start:j].split(':',1)[0].split()
 arguments=' '.join(args);ctx=f'actual_context12_{i}';th=f'actual_caller_binding12_{i}'
 context=head.replace('def '+name,'def '+ctx+' (operation : '+ty+')',1)+':='+re.sub(re.escape(callee)+r'(?![\w.])','operation',body)
 s='import PV_B3P_P227_14\nimport PV_B3P_InternalBinding12227\nimport PV_B3P_ValueCallerBridge12227\nimport PV_B3P_PatternBinding12227\nimport PV_B3P_Operations12227\n'+h+context+'\n'
 s+=f'''theorem {th} {pars}:
    @{name} {arguments} = @{ctx} {source} {arguments} :=
  congrArg (fun (operation : {ty}) => @{ctx} operation {arguments}) {law}
#print axioms {th}
end PV_B3P_Binding12227
'''
 mod=f'PV_B3P_ActualCaller12{i}227';files[mod]=s;rows.append(dict(module=mod,caller=name,callee=callee,theorem=th,credit='actual model caller substitution; complete source association still separately required'))
for m,s in files.items():
 p=L/(m+'.lean')
 if '--check'in sys.argv:assert p.read_text()==s,m
 else:p.write_text(s)
if '--check'not in sys.argv:(D/'resume12/actual-caller-modules.json').write_text(json.dumps(rows,indent=2)+'\n')
