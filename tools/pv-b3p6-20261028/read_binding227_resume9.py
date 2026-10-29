"""Actual-body contexts: substitute one opaque read implementation at every call.
These are read-transformation laws, never a claim that unrolling is discharged.
"""
from pathlib import Path
import re,json,hashlib,sys
D=Path('evidence/pv-b3p6-20261028');L=D/'lean';O=D/'resume9'
files={};rows=[]
header='namespace PV_B3P_Binding9227\nopen Aeneas Aeneas.Std PV_B3P_227 Result ControlFlow Error\nset_option autoImplicit false\n'
files['PV_B3P_ReadFunctions9227']='import PV_B3P_HornerBodyBinding8227\n'+header.replace(' Result ControlFlow Error','')+'''
theorem read_function_binding :
    @reference_terminal.read227 =
      (fun {N : Usize} (values : Array aspis_core.field.QM31 N) (i : Usize) => Array.index_usize values i) := by
  funext N values i
  exact PV_B3P_Success227.read_helper_binding8 values i

theorem digest_function_binding :
    reference_terminal.digest227 =
      (fun (values : Array (Array U32 8#usize) 20#usize) (i : Usize) => Array.index_usize values i) := by
  funext values i
  exact PV_B3P_Success227.digest_helper_binding8 values i

#print axioms read_function_binding
#print axioms digest_function_binding
end PV_B3P_Binding9227
'''
targets=[('PV_B3P_P227_08','reference_terminal.validate_transition_loop.body','digest'),('PV_B3P_P227_09','reference_terminal.sum_interval227_loop.body','read'),('PV_B3P_P227_09','reference_terminal.absorption_lanes_literal','read'),('PV_B3P_P227_09','reference_terminal.semantic_initial_and_absorption','read'),('PV_B3P_P227_10','reference_terminal.add_value_lanes','read'),('PV_B3P_P227_11','reference_terminal.public_digest_lanes','digest')]
for number,(imp,name,kind) in enumerate(targets):
 raw=(L/(imp+'.lean')).read_text();m=re.search(r'^def '+re.escape(name)+r'\b([\s\S]*?)(?=^/-- |^end |\Z)',raw,re.M);assert m,name
 text=m[0].strip();declaration,body=text.split(':=',1);params=declaration[len('def '+name):].strip();end=0;args=[]
 while end<len(params)and params[end]in'({':
  begin=end;depth=1;end+=1
  while depth:depth+=(params[end]in'({')-(params[end]in')}');end+=1
  group=params[begin:end];names=group[1:group.index(':')].split();args.extend(('('+n+':='+n+')')if group[0]=='{' else n for n in names)
  while end<len(params)and params[end].isspace():end+=1
 binders=params[:end];rtype=params[end:];assert rtype.startswith(':')
 argtext=' '.join(args);base=name.replace('.','_');ctx=base+'_read_context9';direct=base+'_direct_read9';law=base+'_read_binding9'
 readtype='({N : Usize} → Array aspis_core.field.QM31 N → Usize → Result aspis_core.field.QM31)' if kind=='read'else'(Array (Array U32 8#usize) 20#usize → Usize → Result (Array U32 8#usize))'
 needle='reference_terminal.'+kind+'227';assert needle in body
 contextbody=body.replace(needle,'source_read');module=f'PV_B3P_ReadBody9{number:02d}227'
 reader_arg = f'(fun (source_read : {readtype}) => {ctx} @source_read {argtext})' if kind=='read' else f'(fun source_read => {ctx} source_read {argtext})'
 s=f'import {imp}\nimport PV_B3P_ReadFunctions9227\n'+header+f'''\n/-- Exact emitted body context; only the immutable-read callee is abstracted. -/
def {ctx} (source_read : {readtype}) {binders} {rtype} := {contextbody}

def {direct} {binders} {rtype} :=
  {ctx} (fun values i => Array.index_usize values i) {argtext}

theorem {law} {binders} :
    {name} {argtext} = {direct} {argtext} :=
  congrArg {reader_arg} {kind}_function_binding

#print axioms {law}
end PV_B3P_Binding9227
'''
 files[module]=s
 rows.append(dict(module=module,body=name,source_module=imp,source_module_sha256=hashlib.sha256(raw.encode()).hexdigest(),abstracted_callee=needle,occurrences=body.count(needle),theorem=law,proof='congrArg actual-body-context named read function equality; no recurrence or field reduction',credit='read substitution ONLY; unroll/copy/frame/mask/grouping obligations retained'))
for m,s in files.items():
 p=L/(m+'.lean')
 if '--check'in sys.argv:assert p.read_text()==s,m
 else:p.write_text(s)
p=O/'read-body-bindings.json'
if '--check'in sys.argv:assert json.loads(p.read_text())==rows
else:p.write_text(json.dumps(rows,indent=2)+'\n')
print(json.dumps(dict(modules=list(files),bodies=len(rows),read_sites=sum(r['occurrences']for r in rows))))
