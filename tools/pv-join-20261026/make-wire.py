from pathlib import Path
import re,json
r=Path(__file__).resolve().parents[2];p=r/'docs/research/v8-r0-zk-20261009/lean/R1Z';e=r/'evidence/pv-join-20261026/wire'
rows=json.loads((e/'rows-before.json').read_text());laws=[x['theorems'][0] for x in rows if x['theorems']]+['R1Z.PV_CB3_Op51Arbitrary.op51_source']
sel='''import R1Z.PV_Join_AggregateCaller
import R1Z.PV_CB_CandidateDictionary
import R1Z.PV_CB3_Op120Source
import R1Z.PV_CB3_Op51Arbitrary
import R1Z.ProverRwBodyReservationTransport
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_Join_Wire_Selection
open Aeneas Aeneas.Std Result ProverRwFull
abbrev native := PV_CB_Op229Transport.native
/-- Current exact source selections on the historical P6 aggregate baseline.
This definition changes proof-level callback selection, never shipped code. -/
@[reducible] def installed (base : ExternalTypes) (ops : @ExternalFuns (native base)) :
    @ExternalFuns (native base) :=
  letI : ExternalTypes := native base
  {PV_CB_CandidateDictionary.selected base (PV_Join_AggregateCaller.selected ops) with
    op51 := @ExternalFuns.op51 _ (PV_CB3_Op51Source.selected ops),
    op120 := @ExternalFuns.op120 _ (PV_CB3_Op120Source.selected ops)}
/-- Preserve the checked reservation/context route after installing source laws. -/
@[reducible] def selected (base : ExternalTypes) (ops : @ExternalFuns (native base)) :=
  @ProverRwOuterGuardLeaves.selected (native base) (installed base ops)
end R1Z.PV_Join_Wire_Selection
'''
(p/'PV_Join_Wire_Selection.lean').write_text(sel)
items=[]
for law in laws:
 ns,t=law.rsplit('.',1);mod=ns.split('.')[-1];text=(p/(mod+'.lean')).read_text();op=int(re.search(r'op(\d+)_source',t)[1])
 # Capture complete declared type, separating the proof at its final declaration delimiter.
 start=text.index('theorem '+t+' ')+len('theorem '+t+' ')
 tail=text[start:];decl=tail[:tail.index(' :=')]
 if op==229:
  first='(base : ExternalTypes) (ops : @ExternalFuns (native base))';assert decl.startswith(first);decl=decl[len(first):]
  proof=f'{ns}.{t} base ops a b'
 else:
  first='(ops : ExternalFuns)';assert decl.startswith(first),(law,decl[:100]);decl=decl[len(first):]
  binders=decl[:decl.index(' :\n') if ' :\n' in decl else decl.index(' :')]
  # Collect explicit argument names only (implicit Type binders are inferred).
  args=[]
  for names,typ in re.findall(r'\(([^():]+)\s*:\s*([^()]*(?:\([^()]*\)[^()]*)*)\)',binders):
   args.extend(names.strip().split())
  proof=ns+'.'+t+' ops'+(' '+' '.join(args) if args else '')
 # split at top-level colon, not binder annotation
 depth=0;split=None
 for i,c in enumerate(decl):
  if c in '({[':depth+=1
  elif c in ')}]':depth-=1
  elif c==':' and depth==0:split=i;break
 assert split is not None,(law,decl)
 binders=decl[:split].strip();eq=decl[split+1:].strip()
 # Use exact original opens plus source namespace for its local aliases.
 opens=' '.join(re.findall(r'^open (.+)$',text,re.M));opens=opens.replace('ControlFlow Error','')
 # Replace only operation's selected LHS, keeping extracted RHS verbatim.
 # LHS selection varies by source file.
 lhs,rhs=eq.split(' =',1)
 # LHS ends with the selected op application; retain its argument suffix.
 suffix=lhs[lhs.index('.op'+str(op))+len('.op'+str(op)):]
 eq='(PV_Join_Wire_Selection.selected base ops).op'+str(op)+suffix+' ='+rhs
 if op==229:binders=binders.replace('Late base','PV_CB_Op229Transport.Late base')
 body=f'''import R1Z.PV_Join_Wire_Selection
import {ns}
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_Join_Wire_Op{op}
open {opens} {mod}
/-- Exact selected-operation source equation; original domain and Result retained. -/
theorem {t} (base : ProverRwFull.ExternalTypes)
    (ops : @ProverRwFull.ExternalFuns (PV_Join_Wire_Selection.native base)) :
    letI : ProverRwFull.ExternalTypes := PV_Join_Wire_Selection.native base
    '''+('∀ '+binders+',\n    ' if binders else '')+eq+' := by\n  letI : ProverRwFull.ExternalTypes := PV_Join_Wire_Selection.native base\n'
 # Extract binder names robustly from top-level parenthetical groups.
 explicit=[];allnames=[];depth=0;beg=0
 for i,c in enumerate(binders):
  if c in '({':
   if depth==0:beg=i
   depth+=1
  elif c in ')}':
   depth-=1
   if depth==0:
    names=binders[beg+1:i].split(':',1)[0].strip().split();allnames+=names
    if binders[beg]=='(':explicit+=names
 if op==229:proof=ns+'.'+t+' base ops '+' '.join(explicit)
 else:proof=ns+'.'+t+' ops'+(' '+' '.join(explicit) if explicit else '')
 if allnames:body+='  intro '+' '.join(allnames)+'\n'
 body+='  exact '+proof+'\n#print '+t+'\n#print axioms '+t+'\nend R1Z.PV_Join_Wire_Op'+str(op)+'\n'
 (p/f'PV_Join_Wire_Op{op}.lean').write_text(body)
 items.append(dict(op=op,source_law=law,module=f'R1Z.PV_Join_Wire_Op{op}',theorem=f'R1Z.PV_Join_Wire_Op{op}.{t}',binders=binders,equation=eq,opens=opens+' '+mod))
(e/'operations.json').write_text(json.dumps(items,indent=2)+'\n')
print('Generated selection and',len(items),'exact consumers')
