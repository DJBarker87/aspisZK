"""NFY method: exact body transport and shared-owner reuse, never owner copies."""
from pathlib import Path
import json,re,hashlib,sys
E=Path(__file__).resolve().parent;P=E.parent/'slice-s-retarget-20261104'
x=json.loads((E/'NGE_INPUTS.json').read_text());G=json.loads((E/'NGE_SOURCE_GRAPH.json').read_text());F=json.loads((P/'NFY_SOURCE_GRAPH.json').read_text())
reuse=x['reused_module_map'].copy();ren=x['reused_namespace_map'].copy();shared=[]
for n in x['order']:
 if n.startswith('S2K_'):
  other='JHb_'+n;assert other in reuse
  # Generated/shared declarations already supplied by NFY, not retargeted.
  body=lambda s:'\n'.join(l for l in s.splitlines() if not l.startswith('import '))+'\n'
  assert body(G[n]['source'])==body(F[other]['source']),(n,'shared owner body drift')
  shared.append(dict(module=n,reused_source=other,target=reuse[other],original_sha256=G[n]['sha256'],adopted_sha256=hashlib.sha256(F[other]['source'].encode()).hexdigest(),nonimport_bodies_byte_identical=True,body_sha256=hashlib.sha256(body(G[n]['source']).encode()).hexdigest()))
  reuse[n]=reuse[other]
order=[n for n in x['order'] if n not in reuse]
ren.update({n:'NGE_'+n for n in order});owner=dict(reuse,**{n:'NGE_'+n for n in order})
pat=re.compile(r'(?<![A-Za-z0-9_])('+'|'.join(map(re.escape,sorted(ren,key=len,reverse=True)))+r')(?![A-Za-z0-9_])')
def emit(n,t):
 if '--check' in sys.argv:assert (E/n).read_text()==t,n
 else:(E/n).write_text(t)
records=[]
for n in order:
 r=G[n];body='\n'.join(l for l in r['source'].splitlines() if not l.startswith('import '))+'\n';after=pat.sub(lambda m:ren[m.group()],body)
 qualify=('open AspisR1TerminalDecoder' in body or 'Result AspisR1TerminalDecoder' in body) and 'core.result.Result.map_err' in body
 if qualify:after=re.sub(r'(?<![A-Za-z0-9_.])core.result.Result.map_err','AspisR1TerminalDecoder.core.result.Result.map_err',after)
 imports=list(dict.fromkeys(['Lean']+[owner.get(d,d) for d in r['imports']]))
 audit='''\nrun_cmd do
 let env ← Lean.getEnv
 env.constants.toList.forM fun (n, ci) => do
  if ci.isTheorem && (env.getModuleIdxFor? n).isNone then
   Lean.Elab.Command.elabCommand (← `(command| #print axioms $(Lean.mkIdent n)))
'''
 emit('NGE_'+n+'.lean',''.join('import '+d+'\n' for d in imports)+'\n'+after+audit)
 records.append(dict(source_module=n,source_path=r['path'],source_sha256=r['sha256'],source_line_range=r['line_range'],target_module='NGE_'+n,imports_before=r['imports'],imports_after=imports,before_body=body,after_body=after,original_body_sha256=hashlib.sha256(body.encode()).hexdigest(),transformed_body_sha256=hashlib.sha256(after.encode()).hexdigest(),changes=['imports','owner-qualified identifiers']+(['fully qualify canonical emitted decoder map_err owner'] if qualify else [])))
emit('NGE_PROVENANCE.json',json.dumps(dict(order=order,module_owner=owner,namespace_map=ren,shared_owner_reuse=shared,files=records),indent=1)+'\n')
print(json.dumps(dict(modules=len(order),shared_reused=len(shared),order=order)))
