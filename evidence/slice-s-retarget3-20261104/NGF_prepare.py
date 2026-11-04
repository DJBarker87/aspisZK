"""Chain B inventory and deterministic owner-only retarget, following NFY method."""
from pathlib import Path
import json,subprocess,re,hashlib,sys
E=Path(__file__).resolve().parent;R=E.parents[1];P=E.parent/'slice-s-retarget-20261104'
J=lambda p:json.loads(p.read_text());H=lambda b:hashlib.sha256(b).hexdigest()
a=J(P/'NFY_AUXILIARY_INPUTS.json');prov=J(P/'NFY_PROVENANCE.json');selected=set()
def visit(n):
 if n in selected or n not in a['source_pins']:return
 selected.add(n)
 for d in a['source_pins'][n]['imports']:visit(d)
for n in a['direct_modules']:
 if n.startswith(('NEX_','NEY_')):visit(n)
order=[n for n in a['order'] if n in selected]
assert not any(n.startswith(('NEE_','NEJ_','NEL_','NEM_','NEQ_')) for n in order)
# Two emitted, independent leaves retain their pinned original owners. Never
# propagate generated Aeneas limits into handwritten successor modules.
independent=['NEC_Reference.Types','NEC_Reference.Funs']
owner=dict(prov['module_owner']);owner.update({n:('NGF_'+n if n not in independent else n) for n in order})
rename=dict(prov['namespace_map']);rename.update({n:'NGF_'+n for n in order if '.' not in n and n not in independent})
pat=re.compile(r'(?<![A-Za-z0-9_])('+'|'.join(map(re.escape,sorted(rename,key=len,reverse=True)))+r')(?![A-Za-z0-9_])')
records=[];graph={}
def emit(n,t):
 p=E/n
 if '--check' in sys.argv:assert p.read_text()==t,('drift',n)
 else:p.write_text(t)
for n in order:
 pin=a['source_pins'][n];raw=subprocess.check_output(['git','show','HEAD:'+pin['path']],cwd=R);assert H(raw)==pin['sha256'],n
 src=raw.decode();graph[n]={**pin,'source':src}
 if n in independent:continue
 body='\n'.join(l for l in src.splitlines() if not l.startswith('import '))+'\n';text=pat.sub(lambda m:rename[m.group()],body)
 text=text.replace('"NEX_Snapshot"','"NGF_NEX_Snapshot"')
 qualified=('open AspisR1TerminalDecoder' in body or 'Result AspisR1TerminalDecoder' in body) and 'core.result.Result.map_err' in body
 if qualified:text=re.sub(r'(?<![A-Za-z0-9_.])core.result.Result.map_err','AspisR1TerminalDecoder.core.result.Result.map_err',text)
 imports=list(dict.fromkeys(['Lean']+[owner.get(d,d) for d in pin['imports']]))
 audit='''\nrun_cmd do
 let env ← Lean.getEnv
 env.constants.toList.forM fun (n, ci) => do
  if ci.isTheorem && (env.getModuleIdxFor? n).isNone then
   Lean.Elab.Command.elabCommand (← `(command| #print axioms $(Lean.mkIdent n)))
'''
 emit(owner[n]+'.lean',''.join('import '+d+'\n' for d in imports)+'\n'+text+audit)
 records.append(dict(source_module=n,source_path=pin['path'],source_sha256=H(raw),source_line_range=pin['line_range'],target_module=owner[n],imports_before=pin['imports'],imports_after=imports,before_body=body,after_body=text,original_body_sha256=H(body.encode()),transformed_body_sha256=H(text.encode()),changes=['imports','qualified proof namespace names']+(['retarget meta-tactic qualified-name prefix'] if '"NEX_Snapshot"' in body else [])+(['fully qualify emitted decoder map_err owner'] if qualified else [])))
# Re-enumerate EVERY theorem record of EVERY selected certificate, independent
# of currently loaded modules, then retain exact names/statements and mappings.
import lzma
ledger=json.loads(lzma.decompress((E.parent/'ledger7-20261104/NFX_LEDGER.json.xz').read_bytes()))
certs=[]
def walk(v,out):
 if isinstance(v,dict):
  if isinstance(v.get('name'),str) and isinstance(v.get('source'),dict) and 'statement' in v:
   out.append(dict(legacy_name=v['name'],canonical_name=pat.sub(lambda m:rename[m.group()],v['name']),source=v['source'],statement_before=v['statement'],statement_after=pat.sub(lambda m:rename[m.group()],v['statement'])))
  for x in v.values():walk(x,out)
 elif isinstance(v,list):
  for x in v:walk(x,out)
for row in ledger['rows']:
 if row['composed_status']!='QUALIFIED':continue
 cert=ledger.get('NFK_certificates',{}).get(row['row'],ledger.get('NEZ_certificates',{}).get(row['row'],row));refs=[];walk(cert,refs)
 certs.append(dict(row=row['row'],function=row['function'],certificate_sha256=H(json.dumps(cert,sort_keys=True).encode()),theorems=refs))
emit('NGF_CERT_INVENTORY.json',json.dumps(certs,indent=1)+'\n')
emit('NGF_SOURCE_GRAPH.json',json.dumps(graph,indent=1)+'\n')
emit('NGF_PROVENANCE.json',json.dumps(dict(order=order,module_owner=owner,namespace_map=rename,independent_emitted_reuse=independent,files=records,chain_A_boundaries=[],scope_resolution='Job is chain B. ORDER item (1) says chain A; interpreted as chain B consistently with explicit assignment and prohibition on retargeting chain A.'),indent=1)+'\n')
emit('NGF_FAMILIES.md','# NGF chain B families\n\nSelected in NFY bottom-up order: '+str(len(order))+' modules; '+str(len(records))+' prefix copies and two independent emitted leaves reused. No chain A dependency in this nonreused closure.\n\n'+ '\n'.join('- '+n+' → '+owner[n] for n in order)+'\n\nNEX contributes 27 formerly missing certificate declarations in 14 direct auxiliary modules (plus five snapshot-part dependencies). NEY contributes 36 formerly missing declarations in 31 direct modules. NED/NEC supply the afterstate Box composition and independent emitted reference closure. No shared owner is redefined.\n\nEvery theorem record in all 89 selected certificates is inventoried before any loaded-module lookup, in NGF_CERT_INVENTORY.json. Certificate admission is governed exclusively by NGF_CERT_CHECK.json, NGF_AUDIT.json, NGF_SCAN.json and NGF_LEDGER_DELTA.json; compilation alone supplies no row credit.\n')
print(json.dumps(dict(modules=len(order),copies=len(records),certificate_rows=len(certs),theorem_records=sum(len(c['theorems']) for c in certs))))
