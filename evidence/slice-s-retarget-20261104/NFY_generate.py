"""Prefix-owned copies; only imports and owner-qualified identifiers change."""
from pathlib import Path
import json,re,hashlib,sys,functools
E=Path(__file__).resolve().parent;P=E.parent/'ledger7-20261104'
G=json.loads((E/'NFY_SOURCE_GRAPH.json').read_text());rows=json.loads((P/'NFX_S_PACKET_PATHS.json').read_text())
admitted={r['module'] for r in map(json.loads,(P/'NFX_LOADED_scan.jsonl').read_text().splitlines())}
reuse=json.loads((E/'NFY_CANONICAL_REUSE.json').read_text())
N=json.loads((E.parent/'slice-q-phase-20261104/NFN_RETARGET_PROVENANCE.json').read_text());S=json.loads((E.parent/'slice-q-accum-20261104/NFS_RETARGET_PROVENANCE.json').read_text())
reuse.update(N['module_owner']);reuse.update(S['owner']);rename=dict(S['namespace_map'])
independent=['JHb_S2K_ResultBytes','NDM_Reference.Types','NDM_Reference.Funs','NDM_GateRef.Types','NDM_GateRef.Funs','NDM_SnapshotRef.Types','NDM_SnapshotRef.Funs']
reuse.update({n:n for n in independent})
# These imports bring no used declaration into the retained bodies. The
# replacement owners provide every referenced carrier/function/lemma.
overrides={'NEE_M31SerializerDomain':['AspisR1AdapterReconstruct.Funs'],'NCA_SerializerWindow':['LPi_EWriter','KMX_CopyMeaning']}
order=[];seen=set()
def visit(n):
 if n in seen or n in admitted or n in reuse:return
 seen.add(n)
 assert n in G,('missing source',n)
 for d in overrides.get(n,G[n]['imports']):visit(d)
 order.append(n)
# Serializer terminals first, then declaration decode and all other packets.
starts=['NEE_M31SerializerDomain','NFD_WideSerialization','NEQ_DecodeScalar','NEQ_CommonDecode','NEQ_PaymentDecode']
starts+=sorted({m for r in rows for m in r['referenced_modules']})
for n in starts:visit(n)
rename.update({n:'NFY_'+n for n in order if '.' not in n})
pattern=re.compile(r'(?<![A-Za-z0-9_])('+'|'.join(map(re.escape,sorted(rename,key=len,reverse=True)))+r')(?![A-Za-z0-9_])')
groups=[];current=[];lines=0
for n in order:
 size=len(G[n]['source'].splitlines())
 if current and (lines+size>750 or n in ['NEE_M31SerializerDomain','LPi_EWriter','NBG_WriterPorts','NCA_SerializerWindow','NFD_WideSerialization'] or current[-1] in ['NEE_M31SerializerDomain','NFD_WideSerialization']):groups.append(current);current=[];lines=0
 current.append(n);lines+=size
if current:groups.append(current)
# L029 heartbeat failure: isolate the terminal validator declaration.
split=[]
for ns in groups:
 if 'NBN_StatementResult' in ns:
  j=ns.index('NBN_StatementResult');split += [xs for xs in [ns[:j],[ns[j]],ns[j+1:]] if xs]
 else:split.append(ns)
groups=split
# Attribute registration must finish in an imported module before use.
split=[]
for ns in groups:
 if 'JHd_Discriminant' in ns:
  j=ns.index('JHd_Discriminant')+1;split += [xs for xs in [ns[:j],ns[j:]] if xs]
 else:split.append(ns)
groups=split
# L052: isolate the two failing request declarations before replay.
for cut in ['JHd_RequestCommon','JHd_RequestPayload','JHf_RawStatementDomainGuard']:
 split=[]
 for ns in groups:
  if cut in ns:
   j=ns.index(cut);split += [xs for xs in [ns[:j],[ns[j]],ns[j+1:]] if xs]
  else:split.append(ns)
 groups=split
groups=[[n for n in ns if n not in independent] for ns in json.loads((E/'NFY_LAYOUT.json').read_text())]
assert all(groups)
owner={n:f'NFY_Part{i:03}' for i,ns in enumerate(groups) for n in ns};owner.update(reuse)
records=[]
def emit(n,t):
 p=E/n
 if '--check' in sys.argv:assert p.read_text()==t,('generated drift',str(p))
 else:p.write_text(t)
for i,names in enumerate(groups):
 module=f'NFY_Part{i:03}';imports=['Lean'];bodies=[]
 for n in names:
  r=G[n];src=r['source'];body='\n'.join(l for l in src.splitlines() if not l.startswith('import '))+'\n';text=pattern.sub(lambda m:rename[m.group()],body)
  qualify = ('open AspisR1TerminalDecoder' in body or 'Result AspisR1TerminalDecoder' in body) and 'core.result.Result.map_err' in body
  text=text.replace('"NBN_AfterDecode"','"NFY_NBN_AfterDecode"')
  if qualify:text=re.sub(r'(?<![A-Za-z0-9_.])core.result.Result.map_err', 'AspisR1TerminalDecoder.core.result.Result.map_err',text)
  request_qualify='open AspisR20Request' in body and 'core.result.Result.map_err' in body
  if request_qualify:text=re.sub(r'(?<![A-Za-z0-9_.])core.result.Result.map_err', 'AspisR20Request.core.result.Result.map_err',text)
  adapter_qualify=('open AspisR1AdapterReconstruct' in body or 'Result AspisR1AdapterReconstruct' in body) and 'core.result.Result.map_err' in body
  if adapter_qualify:text=re.sub(r'(?<![A-Za-z0-9_.])core.result.Result.map_err','AspisR1AdapterReconstruct.core.result.Result.map_err',text)
  for d in overrides.get(n,r['imports']):
   d=owner.get(d,d)
   if d!=module and d not in imports:imports.append(d)
  bodies.append(f'-- BEGIN copied {n}: {r["path"]}\n'+text+f'-- END copied {n}\n')
  # Exact before/after statements, including definitions and proof text, retained
  # in source graph and transformed body. No hypothesis is removed.
  records.append(dict(source_module=n,source_path=r['path'],source_sha256=hashlib.sha256(src.encode()).hexdigest(),source_line_range=[1,len(src.splitlines())],target_module=module,original_body_sha256=hashlib.sha256(body.encode()).hexdigest(),transformed_body_sha256=hashlib.sha256(text.encode()).hexdigest(),imports_before=r['imports'],imports_after=[owner.get(d,d) for d in overrides.get(n,r['imports'])],changes=['imports','qualified proof namespace names']+(['fully qualify emitted decoder map_err owner'] if qualify or request_qualify or adapter_qualify else [])+(['retarget meta-tactic qualified-name prefix'] if '"NBN_AfterDecode"' in body else []),before_body=body,after_body=text))
 audit='''\nrun_cmd do
 let env ← Lean.getEnv
 env.constants.toList.forM fun (n, ci) => do
  if ci.isTheorem && (env.getModuleIdxFor? n).isNone then
   Lean.Elab.Command.elabCommand (← `(command| #print axioms $(Lean.mkIdent n)))
'''
 emit(module+'.lean',''.join('import '+d+'\n' for d in imports)+'\n'+''.join(bodies)+audit)
emit('NFY_PROVENANCE.json',json.dumps(dict(order=order,groups=groups,module_owner=owner,namespace_map=rename,import_overrides=overrides,independent_emitted_reuse=independent,files=records),indent=1)+'\n')
print(json.dumps(dict(copies=len(order),parts=len(groups),lines=sum(len(G[n]['source'].splitlines()) for n in order),first=groups[:7])))
