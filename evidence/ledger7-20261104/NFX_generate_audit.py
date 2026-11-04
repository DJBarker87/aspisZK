"""Generate one combined certificate forest and NEP-identical raw audit driver."""
from pathlib import Path
import json,re,hashlib
E=Path(__file__).resolve().parent;R=E.parents[1]
q=R/'evidence/slice-q-accum-20261104';s=R/'evidence/slice-s-compose12-20261104';d=R/'evidence/slice-d-define-20261104'
# Include every S and Q predecessor root, not just final theorem names.
qr=json.loads((q/'NFS_AUDIT_ROOTS.json').read_text())['roots']
sr=[r['root'] for r in json.loads((s/'NFJ_AUDIT.json').read_text())['results']]
# Add all dot/control and geometry/raw roots in their coherent, retargeted forms.
mr=json.loads((R/'evidence/slice-q-mul9-20261104/NFM_AUDIT_ROOTS.json').read_text())['roots']
nr=json.loads((R/'evidence/slice-q-phase-20261104/NFN_AUDIT_ROOTS.json').read_text())
# NFN's standalone list includes legacy declarations superseded by NFS retargets;
# keep its geometry root forest, as admitted by NFN, only if not legacy NEV.
nr=[x for x in nr if not x.startswith(('NEV_','NEI_','NEG_','NEW_','NFB_','AspisR1.NEV_'))]
certs=json.loads((d/'NFQ_CLOSED.json').read_text())['functions'];dr=[r['lean_root'] for r in certs]
# After measured legacy qualification, the S root packets are not admitted.
# Preserve only independently coherent S helper packet forests.
helper_modules=['NEQ_UnwrapDomains','NEX_Exact']
helper_roots=[]
# Exact named proof references in the independently retained helper certificates.
base=json.loads(__import__('lzma').decompress((R/'evidence/ledger6-20261104/NFK_LEDGER.json.xz').read_bytes()))
packet_paths=json.loads((E/'NFX_S_PACKET_PATHS.json').read_text())
retained=[x for x in packet_paths if not x['legacy_paths']]
for row in retained:
 cert=base['NEZ_certificates'][row['row']]
 def visit(x):
  if isinstance(x,dict):
   if isinstance(x.get('name'),str) and any(x['name'].startswith(m+'.') for m in helper_modules):helper_roots.append(x['name'])
   for v in x.values():visit(v)
  elif isinstance(x,list):
   for v in x:visit(v)
 visit(cert)
roots=sorted(set(qr+mr+nr+dr+helper_roots+['AspisR1.RPx_Deployed.deployed']))
imports=['RPx_Deployed','NFS_COMBINED_IMPORT']+sorted({x.rsplit('.',1)[0] for x in dr}|set(helper_modules))
# Several predecessor audits imported support modules dynamically. Include their
# complete forests too, instead of dropping a root because it is not transitively
# imported by the final packet theorem.
known={p.stem for p in (R/'evidence').glob('*/*.lean')}
for root in roots:
 bits=root.split('.');module=bits[1] if bits[0]=='AspisR1' else bits[0]
 if module in known and module not in imports and not module.startswith('NFS_NEV_'):imports.append(module)
# Selected audit manifests define the exact theorem subjects; no theorem introduced.
combined='\n'.join('import '+m for m in imports)+'\n'+'\n'.join('#print axioms '+r for r in roots)+'\n'
(E/'NFX_COMBINED_IMPORT.lean').write_text(combined)
groups=[roots[i:i+4] for i in range(0,len(roots),4)]
manifest=dict(headline='AspisR1.RPx_Deployed.deployed',imports=imports,roots=roots,groups=groups,source_forests=dict(S_retained_helpers=sorted(set(helper_roots)),S_qualified_excluded=sr,Q=qr,dots=mr,geometry=nr,D_closed=dr),legacy_forest_imported=False)
(E/'NFX_AUDIT_ROOTS.json').write_text(json.dumps(manifest,indent=1)+'\n')
proof=(q/'NFS_ProofDriver.lean').read_text();a=proof.index('  let (modules, roots) :=');b=proof.index('  let env ← importModules',a)
choices=[]
for i,g in enumerate(groups):choices.append(('    if' if i==0 else '    else if')+f' mode == "proof{i}" then\n      (#[`NFX_COMBINED_IMPORT], #['+', '.join('`'+x for x in g)+'])\n')
fixture=proof[proof.index('    else if mode == "fixtures" then',a):b]
proof=proof[:a]+'  let (modules, roots) :=\n'+''.join(choices)+fixture+proof[b:]
# Use the scanner with exactly its audited NFS implementation; only mode/imports/I/O change.
scan=(q/'NFS_Driver.lean').read_text();a=scan.index('  let (modules, roots) :=');b=scan.index('  let env ← importModules',a)
scan=scan[:a]+'  let (modules, roots) := if mode == "scan" then (#[`NFX_COMBINED_IMPORT], #[]) else (#[], #[])\n'+scan[b:]
scan=scan.replace('NFS_EXPECTED_IMPORTS.jsonl','NFX_EXPECTED_IMPORTS.jsonl').replace('NFS_LOADED_scan.jsonl','NFX_LOADED_scan.jsonl')
(E/'NFX_ProofDriver.lean').write_text(proof);(E/'NFX_Driver.lean').write_text(scan)
# Pin byte-identical NEP walker, already compiled as NFA_WALKER.
walker=(R/'evidence/axaudit2-20261102/NEP_WALKER.lean').read_bytes();other=(R/'evidence/slice-q-mul4-20261104/NFA_WALKER.lean').read_bytes();assert walker==other
(E/'NFX_WALKER_PIN.json').write_text(json.dumps(dict(sha256=hashlib.sha256(walker).hexdigest(),path='evidence/axaudit2-20261102/NEP_WALKER.lean',resolved_module='NFA_WALKER'),indent=1)+'\n')
# Baseline import tables from actual checked scans, plus exact new module sources.
tables={};conflicts=[]
for path in [R/'evidence/slice-q-phase-20261104/NFN_EXPECTED_IMPORTS.jsonl',q/'NFS_EXPECTED_IMPORTS.jsonl',R/'evidence/slice-q-mul9-20261104/NFM_EXPECTED_IMPORTS.jsonl']:
 if not path.exists():continue
 for line in path.read_text().splitlines():
  x=json.loads(line);m=x['module'];im=x['imports']
  if m in tables and tables[m]!=im:conflicts.append(dict(module=m,old=tables[m],new=im,source=str(path.relative_to(R))))
  tables[m]=im
# S expected tables may be missing from its old packet; exact committed Lean
# import lines supply those module-local baselines without using loaded scan output.
for directory in [s,d,*[R/'evidence'/n for n in ['slice-s-compose5-20261102','slice-s-compose6-20261102','slice-s-compose7-20261103','slice-s-compose8-20261104','slice-s-compose9-20261104','slice-s-compose10-20261104','slice-s-compose11-20261104']],E]:
 for p in directory.glob('*.lean'):
  im=['Init']
  for match in re.finditer(r'^(?:public )?import\s+(?:all\s+)?([\w.]+)',p.read_text(),re.M):
   if match[1] not in im:im.append(match[1])
  if p.stem not in tables or p.stem.startswith(('NFX_','NFQ_','NFJ_','NFH_','NFD_','NEY_','NEX_','NEU_','NEQ_','NEM_')):tables[p.stem]=im
# Imported helper owners absent from aggregate predecessor scans get a
# source baseline, never a baseline copied from this run's loaded environment.
for p in sorted((R/'evidence').glob('*/*.lean')):
 if p.stem in tables:continue
 im=['Init']
 for m in re.finditer(r'^(?:public )?import\s+(?:all\s+)?([\w.]+)',p.read_text(),re.M):
  if m[1] not in im:im.append(m[1])
 tables[p.stem]=im
# These ten namespace/helper objects were not in the predecessor aggregate
# import tables. Derive their baselines from committed accepted sources.
explicit={
 'NBG_Atomic':'evidence/native-tx2c-20261027/NBG_L020/sources/NBG_generated/NBG_Atomic.lean',
 'NBP_Read':'evidence/native-tx2g-20261028/NBP_L027/sources/NBP_generated/NBP_Read.lean'}
for prefix,directory in [('NFQ_Reference','slice-d-define-20261104'),('NFQ_ScanReference','slice-d-define-20261104'),('NCO_Reference','native-cpilot-20261028'),('NCO_ParserRef','native-cpilot-20261028')]:
 for part in ['Types','Funs']:explicit[prefix+'.'+part]='evidence/'+directory+'/'+prefix+'/'+part+'.lean'
baseline_pins=[]
for module,path in explicit.items():
 raw=__import__('subprocess').check_output(['git','show','HEAD:'+path],cwd=R);im=['Init']
 for m in re.finditer(r'^(?:public )?import\s+(?:all\s+)?([\w.]+)',raw.decode(),re.M):
  if m[1] not in im:im.append(m[1])
 if raw.decode().startswith('prelude'):im=[x for x in im if x!='Init']
 tables[module]=im;baseline_pins.append(dict(module=module,path=path,sha256=hashlib.sha256(raw).hexdigest(),imports=im))
(E/'NFX_SCAN_BASELINE_FIX.json').write_text(json.dumps(baseline_pins,indent=1)+'\n')
(E/'NFX_EXPECTED_IMPORTS.jsonl').write_text(''.join(json.dumps(dict(module=m,imports=im))+'\n' for m,im in sorted(tables.items())))
(E/'NFX_IMPORT_BASELINE_CONFLICTS.json').write_text(json.dumps(conflicts,indent=1)+'\n')
print(json.dumps(dict(roots=len(roots),groups=len(groups),imports=imports,baseline_conflicts=len(conflicts))))
