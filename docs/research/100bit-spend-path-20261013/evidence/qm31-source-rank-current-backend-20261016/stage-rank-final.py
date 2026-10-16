from pathlib import Path
import importlib.util,json,shutil
from datetime import datetime,timezone

base=Path('/home/dombarker/project-offloads')
prior=base/'aspis-r1-r18-sampler-rank-consumers-20261016'
rank=base/'aspis-r1-r18-sampler-rank-20261016'
w=base/'aspis-r1-r18-sampler-rank-final-20261016';w.mkdir(exist_ok=True)
shutil.copy2(prior/'rank-runner.py',w/'runner.py')
spec=importlib.util.spec_from_file_location('runner',w/'runner.py');r=importlib.util.module_from_spec(spec);spec.loader.exec_module(r)
snapshot=prior/'external-inputs-rank-consumers.json';data,_=r.verify_snapshot(snapshot)
basekeys=r.external_keys(data)
manifest=json.loads((prior/'sources/SOURCE-MANIFEST.json').read_text())
closure=json.loads((rank/'input-pins/rank-closure.json').read_text())
names=['AspisV8R19.SqueezeSourceExecution','AspisV8R19.SqueezeOracleBridge','AspisV8R19.SamplerWordBridge','R1SamplerByteWord','R1SamplerBytePass']
checked={}
for name in names:
    item=manifest['modules'][name];src=prior/'sources'/item['stage_as']
    rp=prior/'successful-targets'/(name+'.json');receipt=json.loads(rp.read_text())
    objects=r.object_pins(prior/'objects',name,data['olean_header_seal'])
    assert receipt['exit_status']==0 and receipt['axioms']['passed']
    assert receipt['key']['source_sha256']==r.sha(src)==closure['modules'][name]['sha256']
    assert receipt['key']['runtime']==data['runtime_files'] and receipt['key']['options']==['-j1','-M0']
    assert receipt['objects']==objects
    expected={}
    for dep in r.imports(src,implicit_init=True):
        if dep in checked:
            expected[dep]={'receipt_key':r.digest(checked[dep]['key']),'objects':r.object_pins(prior/'objects',dep,data['olean_header_seal'])}
        else:
            expected[dep]={'objects':data['modules'][dep]['objects'],'closure_key':basekeys[dep]}
    assert receipt['key']['imports']==expected,name
    data['modules'][name]={'root':'rank_consumer_checked','source':str(src),'source_sha256':r.sha(src),
        'imports':r.imports(src,implicit_init=True),'objects':objects,
        'build_receipt':{'path':str(rp),'sha256':r.sha(rp)}}
    checked[name]=receipt
data['roots'].insert(0,{'name':'rank_consumer_checked','source':str(prior/'sources'),'objects':str(prior/'objects')})
invalidated=['AspisFormal.CircleGroupOrder','R0C.ModuloField','R1SamplerBlockRank']
rejected={name:data['modules'].pop(name) for name in invalidated}
r.external_keys(data)
data['provenance_files'][str(snapshot)]=r.sha(snapshot)
for f in ['object-imports.jsonl','object-imports.receipt.json','ReadObjectImports.lean']:
    data['provenance_files'][str(prior/f)]=r.sha(prior/f)
data['scope']='Prior exact cached sources plus5 newly checked byte/rank modules. Reject historical CircleGroupOrder object: actual imports Mathlib but current source uses15 focused imports. Invalidate R0C.ModuloField and BlockRank as its only cached dependent chain. Preserve mixed SamplerWordRead failure/exclusions. No Mathlib-root expansion.'
data['captured_utc']=datetime.now(timezone.utc).isoformat()
r.dump(w/'external-inputs-rank-final.json',data)
r.dump(w/'invalidated-cache-records.json',rejected)
sources=w/'sources';sources.mkdir(exist_ok=True);entries={}
for name in invalidated+['R1SourceSamplerByteRank']:
    item=closure['modules'][name]
    src=Path(rejected[name]['source']) if name in rejected else prior/'sources/R1SourceSamplerByteRank.lean'
    assert r.sha(src)==item['sha256']
    dest=sources/(r.stem(name)+'.lean');dest.parent.mkdir(parents=True,exist_ok=True);shutil.copy2(src,dest)
    entries[name]={'source':item['path'],'source_sha256':r.sha(dest),'source_revision':closure['source_revision'],
        'imports':r.imports(dest),'stage_as':r.stem(name)+'.lean','role':'unchanged source; corrected exact source/object provenance and necessary dependent check'}
name='SourceSamplerByteRankAudit';src=prior/'sources'/(name+'.lean');dest=sources/(name+'.lean');shutil.copy2(src,dest)
entries[name]=manifest['modules'][name]
r.dump(sources/'SOURCE-MANIFEST.json',{'format':2,'modules':entries,'topological_order':invalidated+['R1SourceSamplerByteRank',name],'groups':{}})
r.staged(w);r.verify_snapshot(w/'external-inputs-rank-final.json')
print(json.dumps({'targets':list(entries),'external_source_closure_modules':61,'snapshot_sha256':r.sha(w/'external-inputs-rank-final.json'),'source_manifest_sha256':r.sha(sources/'SOURCE-MANIFEST.json')},indent=2))
