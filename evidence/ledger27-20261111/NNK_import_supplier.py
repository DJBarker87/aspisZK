from pathlib import Path
import json,lzma,hashlib,subprocess
E=Path(__file__).resolve().parent;Q=E.parent/'tx2-auth-20261111';name='NMX_R3_RegistrySuppliers';rc=json.loads((Q/'NMX_L961/receipt.json').read_text());source=(Q/(name+'.lean')).read_bytes();h=hashlib.sha256(source).hexdigest();assert rc['exit_status']==0 and rc['source_hashes']['NMX_generated/'+name+'.lean']==h
B='/home/dombarker/project-offloads/codex-cx-ledger8-cache-20261104/NNK_20261111';code=f'''from pathlib import Path
import json,hashlib,shutil
b=Path({B!r});q=Path('/home/dombarker/project-offloads/codex-cx-tx2-auth-20261111');assert hashlib.sha256((q/'NMX_L961/sources/NMX_generated/{name}.lean').read_bytes()).hexdigest()=={h!r}
rows=[]
for p in [q/'NMX_objects/{name}.olean']:
 dst=b/'NMXmissing_seed'/p.name;dst.parent.mkdir(exist_ok=True);shutil.copy2(p,dst);digest=hashlib.sha256(p.read_bytes()).hexdigest();assert hashlib.sha256(dst.read_bytes()).hexdigest()==digest;rows.append(dict(tag='NMXmissing',path=str(p),destination=str(dst),sha256=digest,bytes=p.stat().st_size))
print(json.dumps(rows))
'''
r=subprocess.run(['ssh','-o','ControlMaster=no','-o','ConnectTimeout=15','dombarker@100.108.41.90','python3'],input=code,text=True,capture_output=True);assert r.returncode==0,r.stderr;rows=json.loads(r.stdout)
for stem in ['NNK_CACHE_IMPORTS.json.xz','NNK_CACHE_IMPORTS.json.sha256']:(E/stem.replace('NNK_CACHE_IMPORTS','NNK_CACHE_IMPORTS_INITIAL')).write_bytes((E/stem).read_bytes())
p=E/'NNK_CACHE_IMPORTS.json.xz';x=json.loads(lzma.decompress(p.read_bytes()));x['files']+=rows;raw=json.dumps(x).encode();p.write_bytes(lzma.compress(raw));(E/'NNK_CACHE_IMPORTS.json.sha256').write_text(hashlib.sha256(raw).hexdigest()+'\n')
p=E/'NNK_SEED_INPUTS.json';x=json.loads(p.read_text());x += [dict(tag=r['tag'],path=r['path'],relative=Path(r['path']).name,sha256=r['sha256'])for r in rows];p.write_text(json.dumps(x,indent=1)+'\n')
p=E/'NNK_PATHS.json';x=json.loads(p.read_text());x.insert(0,B+'/NMXmissing_seed');p.write_text(json.dumps(x,indent=1)+'\n')
(E/'NNK_MISSING_MODULE.json').write_text(json.dumps(dict(attempt='NNK_L054',kind='OWN_COMBINED_IMPORT_OMISSION',missing=name+'.selected',source_receipt='NMX_L961',source_sha256=h,source_matches_accepted_snapshot=True,objects=rows,reason='Producer per-root audit310 imports supplier diagnostic; producer combined/export omitted this otherwise accepted pure rfl module. No existing root definition changes. Cache object freshly hashed; exact source/statement audit and standard axioms required in this gate.',remaining65_in54='standard, complete results retained',retry='only missing root added to next bounded window; do not rerun65 completed roots',context_extension='NNK_COMBINED_IMPORT has no declarations; add one disjoint supplier module. NFX + identical previous-object hashes verify no existing graph changed.'),indent=1)+'\n')
# Synchronize only this job cache-import receipt; no shared cache/source edits.
p=E/'NNK_CACHE_IMPORTS.json.xz';script="from pathlib import Path\nPath("+repr(B+'/NNK_CACHE_IMPORTS.json.xz')+").write_bytes(bytes.fromhex("+repr(p.read_bytes().hex())+"))\n";r=subprocess.run(['ssh','-o','ControlMaster=no','dombarker@100.108.41.90','python3'],input=script,text=True,capture_output=True);assert r.returncode==0,r.stderr
