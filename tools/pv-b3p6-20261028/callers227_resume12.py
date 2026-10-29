"""Apply named transformations at the actual extracted caller contexts.
These close caller substitution steps, not the caller's remaining source changes.
"""
from pathlib import Path
import re,json,sys
D=Path('evidence/pv-b3p6-20261028');L=D/'lean';files={};rows=[]
raw=(D/'raw227-composition-resume5/Funs.lean').read_text()
h='namespace PV_B3P_Binding12227\nopen Aeneas Aeneas.Std PV_B3P_227 Result ControlFlow Error\nset_option autoImplicit false\n'
ops=[('preweighted','reference_terminal.add_preweighted',
    '{N : Usize} → Array aspis_core.field.QM31 24#usize → Usize → Array aspis_core.field.QM31 N → Result (Array aspis_core.field.QM31 24#usize)',
    '@source_preweighted12','preweighted_operation_binding12','PV_B3P_PreweightedLoop12227'),
    ('equality','reference_terminal.equality_value',
    'Array aspis_core.field.QM31 10#usize → Array aspis_core.field.QM31 10#usize → Result aspis_core.field.QM31',
    'PV_B3P_Binding9227.source_equality_value',
    '(funext fun left => funext fun right => (PV_B3P_Binding9227.equality_body_binding left right).symm)','PV_B3P_EqualityBinding9227'),
    ('reconstruct','reference_terminal.reconstruct_10',
    'Array aspis_core.field.QM31 16#usize → Result aspis_core.field.QM31',
    'PV_B3P_Binding9227.source_reconstruct',
    '(funext fun view => (PV_B3P_Binding9227.reconstruct_body_binding view).symm)','PV_B3P_ReconstructBinding9227')]
for label,callee,optype,source,law,imp in ops:
 for block in re.split(r'(?=^/-- \[)',raw,flags=re.M):
    m=re.search(r'^def (\S+)',block,re.M)
    if not m:continue
    decl=block[m.start():].strip();head,body=decl.split(':=',1)
    if not re.search(re.escape(callee)+r'\b',body):continue
    name=m[1]
    if name=='reference_terminal.add_value_lanes':
        rows.append(dict(module=f'PV_B3P_Caller12{len(rows):02}227',caller=name,callee=callee,credit='REJECTED whole-body context; do not regenerate or retry',replacement='PV_B3P_ValueCallerStage1207227 / PV_B3P_ValueCallerStage1214227 / PV_B3P_ValueCallerBridge12227'))
        continue
    ctx='context12_'+label+'_'+name.replace('.','_');th='caller12_'+label+'_'+name.replace('.','_')
    params=head[head.index(name)+len(name):]
    # The result colon is the first colon outside a parameter group.
    depth=0;boundary=None
    for i,c in enumerate(params):
        if c in '([{':depth+=1
        elif c in ')]}':depth-=1
        elif c==':' and depth==0:boundary=i;break
    assert boundary is not None,name
    pars=params[:boundary];args=[];depth=0;start=0
    for i,c in enumerate(pars):
        if c in '({':
            if depth==0:start=i+1
            depth+=1
        elif c in ')}':
            depth-=1
            if depth==0:args+=pars[start:i].split(':',1)[0].split()
    assert all(re.fullmatch(r'\w+',a)for a in args),(name,args)
    arguments=' '.join(args)
    context=head.replace('def '+name,'def '+ctx+' (operation : '+optype+')',1)+':='+re.sub(re.escape(callee)+r'\b','operation',body)
    s=f'import PV_B3P_P227_14\nimport {imp}\n'+h+context+'\n'
    s+=f'theorem {th} {pars}:\n    @{name} {arguments} = @{ctx} ({source}) {arguments} :=\n  congrArg (fun (operation : {optype}) => @{ctx} @operation {arguments}) {law}\n'
    s+=f'#print axioms {th}\nend PV_B3P_Binding12227\n'
    mod=f'PV_B3P_Caller12{len(rows):02}227';files[mod]=s
    rows.append(dict(module=mod,caller=name,callee=callee,theorem='PV_B3P_Binding12227.'+th,credit='actual emitted caller substitution by named complete-Result operation equality; other source transformations remain open'))
for m,s in files.items():
 p=L/(m+'.lean')
 if '--check'in sys.argv:assert p.read_text()==s,m
 else:p.write_text(s)
if '--check'not in sys.argv:(D/'resume12/caller-modules.json').write_text(json.dumps(rows,indent=2)+'\n')
print(json.dumps([r['module'] for r in rows]))
