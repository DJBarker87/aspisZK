"""Retain the literal emitted control structure, restoring typed child Boxes.
Only the enumerated call sites become free commands; all Result/ControlFlow
operations remain explicit scalar calls, not assumed successful.
"""
from pathlib import Path
import re,json,hashlib
E=Path(__file__).resolve().parent
plan=json.loads((E/'NMX_FOLD_PLAN.json').read_text())
manifest=json.loads((E/'NMX_STEP_MANIFEST.json').read_text())
changes=[]
rust={'readonlyBuffer','checkpointGuard','readonlyAccount','distinct','data','master','checkpoint','lane','registry'}
for group in range(6):
 text=(E/f'NMX_Actual{group:02d}.lean').read_text()
 defs=re.split(r'\n(?=def t\d{3})',text)[1:]
 out=f'''import NMX_R4_CallProgram
import NMX_ResultSteps
'''+(f'import NMX_R4_CallScript{group+1:02d}\n' if group<5 else '')+f'''set_option autoImplicit false
noncomputable section
namespace NMX_R4_CallScript{group:02d}
open Aeneas Aeneas.Std Result AdapterRw NMX_OwnedPackets NMX_SourceModel NMX_R4_CallProgram
'''
 for d in defs:
  d=d.split('\nend NMX_Actual')[0]
  n=int(re.match(r'def t(\d{3})',d)[1]);st=plan[n-1]
  head,body=d.split(' := do\n',1)
  head=head.replace(': Final',': Program (core.result.Result Auth PE)')
  for v,t in [('master','Master'),('checkpoint','Checkpoint'),('lane','Lane'),('live','Snapshot')]:
   head=head.replace(f'({v} : {t})',f'({v} : Box {t})')
   body=re.sub(r'\b'+v+r'\.(?!payload)',v+'.payload.',body)
  body=re.sub(r'NMX_Actual(\d\d)\.',r'NMX_R4_CallScript\1.',body)
  if n==52:
   body=body.replace('let live : Snapshot := {','let live ← snapshot {')
  else:
   # Each native Result bind is one scalar command, except its enumerated child.
   lines=body.splitlines();i=0;first=True
   while i<len(lines):
    m=re.match(r'(\s*let \w+ ←)\s*(.*)',lines[i])
    if not m:i+=1;continue
    indent=len(lines[i])-len(lines[i].lstrip());j=i+1
    while j<len(lines) and len(lines[j])-len(lines[j].lstrip())>indent:j+=1
    expr='\n'.join([m[2]]+lines[i+1:j]).strip()
    original=expr
    isrust=False
    if first and st['term'].startswith('call '):
     cmd=re.match(r'call \(\.(\w+) (.*)\)',st['term'],re.S)
     assert cmd,st
     name,args=cmd.groups()
     if name in rust:
      expr='child (.'+name+' '+args+')';isrust=True
     elif name=='pda':expr='pda '+args;isrust=True
    if not isrust:
     if expr.startswith('lift '):expr='.ok '+expr[5:]
     expr='scalar ('+expr+')'
    changes.append({'n':n,'original':original,'lifted':expr,'first_call':first})
    lines[i:j]=[m[1]+' '+expr]
    i+=1;first=False
   body='\n'.join(lines)
  # The generic residual operation is still the actual Try/from_residual code.
  body=body.replace('r1_pool_adapter.AuthenticatedAsq8Accounts','Auth')
  body=re.sub(r'(?m)^(\s*)core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual\n(.*)',r'\1scalar (core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual\n\2',body)
  # Close only those residual expressions (one branch at each Rust call).
  if 'scalar (core.result.Result.Insts.' in body:
   idx=body.rfind('residual');body=body[:idx]+'residual)'+body[idx+8:]
  if n==55:
   for old,new in [('master_account','masterAccount'),('checkpoint_account','checkpointAccount'),('selected_lane_account','selectedLaneAccount'),('selected_lane','selectedLane'),('live_snapshot','liveSnapshot')]:
    body=re.sub(r'\b'+old+r'(?=\s*:=)',new,body)
  # Final Rust Results remain complete constructors, in the free return.
  body=re.sub(r'\bok\s*\(core.result.Result\.(Err|Ok)',r'Program.ret (core.result.Result.\1',body)
  # Generic scalar calls may span multiple lines; original branches remain.
  out+='\n'+head+' := do\n'+body+'\n'
 out+=f'end NMX_R4_CallScript{group:02d}\nend\n'
 (E/f'NMX_R4_CallScript{group:02d}.lean').write_text(out)
(E/'NMX_R4_CALL_LIFT.json').write_text(json.dumps({'method':'literal Actual continuation control with explicit Result/ControlFlow steps; typed Boxes restored; enumerated calls only','changes':changes},indent=1)+'\n')
