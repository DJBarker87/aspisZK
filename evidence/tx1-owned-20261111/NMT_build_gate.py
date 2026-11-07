from NMT_formal import *
# Select only current-source passing modules, never a failed elaboration's object.
rcs=[json.loads(l) for l in (E/'NMT_ATTEMPTS.jsonl').read_text().splitlines() if json.loads(l).get('kind')=='lean' and json.loads(l).get('exit_status')==0]
current={}
for r in rcs:
 p=E/(r['module']+'.lean')
 if p.is_file() and sha(p.read_bytes()) in r['source_hashes'].values():current[r['module']]=r
roots=[]
for m,r in current.items():
 for line in r['print_axioms']:
  if line.startswith("'"):
   name=line.split("'")[1]
   if name not in roots:roots.append(name)
modules=sorted(current)
# The canonical ledger24 import is a fixed baseline; audit its headline only.
(E/'NMT_COMBINED_IMPORT.lean').write_text('\n'.join('import '+m for m in ['NLX_COMBINED_IMPORT']+modules)+'\n#check AspisR1.RPx_Deployed.deployed\n')
(E/'NMT_AUDIT_ROOTS.json').write_text(json.dumps(dict(groups=[roots,['AspisR1.RPx_Deployed.deployed']]),indent=1)+'\n')
(E/'NMT_AUDIT_MODULES.json').write_text(json.dumps([modules,['NMT_COMBINED_IMPORT']],indent=1)+'\n')
(E/'NMT_CURRENT_MODULES.json').write_text(json.dumps(dict(modules=modules,roots=roots,passing_sources={m:sha((E/(m+'.lean')).read_bytes()) for m in modules}),indent=1)+'\n')
r=run('NMT_L052','lean','NMT_COMBINED_IMPORT')
if r['exit_status']:raise SystemExit(1)
r=run('NMT_L053','lean','NMT_ProofDriver')
raise SystemExit(r['exit_status'])
