"""Read-only post-audit object pins; validate source and retained cache provenance."""
from pathlib import Path
import hashlib,json,subprocess,shlex
E=Path(__file__).resolve().parent
allpins={}
for attempt in ['KSB_L005','KSB_L006','KSB_L007']:
    modules=set()
    for line in (E/attempt/'stdout.log').read_text().splitlines():
        if line.startswith('KSB_DEP '):modules.add(json.loads(line[8:])['module'])
    roots=json.loads((E/(attempt+'.json')).read_text())['env']['LEAN_PATH'].split(':')
    program='''from pathlib import Path
import hashlib,json
roots=ROOTS
modules=MODULES
out={}
for m in sorted(modules):
 key=m.replace('.','/')+'.olean'
 p=next((Path(r)/key for r in roots if (Path(r)/key).exists()),None)
 if p is None:raise FileNotFoundError(m)
 out[m]=dict(path=str(p),sha256=hashlib.sha256(p.read_bytes()).hexdigest(),bytes=p.stat().st_size)
print(json.dumps(out))
'''.replace('ROOTS',repr(roots)).replace('MODULES',repr(sorted(modules)))
    r=subprocess.run(['ssh','-o','ConnectTimeout=20','dombarker@100.108.41.90','python3 -'],input=program,capture_output=True,text=True)
    if r.returncode:raise SystemExit('read-only object pin transport failed; no job submitted: '+r.stderr)
    allpins[attempt]=json.loads(r.stdout)
(E/'KSB_kernel_object_pins.json').write_text(json.dumps(dict(timing='post-audit read-only pins; not retroactive pre-launch pins',environments=allpins),indent=2)+'\n')

manifest=json.loads(Path('evidence/extraction-assoc24-20261027/XSf_DEPENDENCY_CLOSURE.json').read_text())['modules']
cache6=json.loads(Path('evidence/extraction-assoc23-20261027/XSe_CACHE_END.json').read_text())
cache4=json.loads(Path('evidence/extraction-assoc22-20261027/XSd_CACHE_END.json').read_text())['objects']
expected={m:r['object']['sha256'] for m,r in manifest.items()}
expected6={Path(k).stem:r['sha256'] for k,r in cache6.items()}
expected4={Path(k).stem:r['sha256'] for k,r in cache4.items()}
checks=[]
for a,pins in allpins.items():
    historical=expected if a=='KSB_L005' else expected6 if a=='KSB_L006' else expected4
    for m,r in pins.items():
        old=historical.get(m)
        checks.append(dict(attempt=a,module=m,object_sha256=r['sha256'],retained_manifest_sha256=old,match=r['sha256']==old if old else None))

ix=json.loads((E/'KSB_sources.json').read_text())
receipts={}
for folder in Path('evidence').glob('extraction-assoc*-20261027'):
    for rp in folder.glob('*_L*/receipt.json'):
        r=json.loads(rp.read_text())
        if r.get('exit_status')!=0:continue
        for src,h in r.get('source_hashes',{}).items():receipts.setdefault((Path(src).stem,h),[]).append(str(rp))
sourcechecks=[]
for m in sorted(set().union(*(set(p) for p in allpins.values()))):
    if m not in ix:continue
    p=Path(ix[m]);h=hashlib.sha256(p.read_bytes()).hexdigest()
    original=manifest.get(m,{}).get('source_hashes',{})
    sourcechecks.append(dict(module=m,path=str(p),sha256=h,accepted_receipts=receipts.get((m,h),[]),
        A2_manifest_source_match=h in original.values() if original else None))
out=dict(object_checks=checks,source_checks=sourcechecks,object_mismatches=[r for r in checks if r['match'] is False],
    objects_without_retained_manifest=[r for r in checks if r['match'] is None],
    sources_without_matching_accepted_receipt=[r for r in sourcechecks if not r['accepted_receipts']],
    source_mismatches=[r for r in sourcechecks if r['A2_manifest_source_match'] is False])
(E/'KSB_provenance.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps({k:len(v) for k,v in out.items()}))
