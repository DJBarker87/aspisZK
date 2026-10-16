from pathlib import Path
import importlib.util, json, shutil
from datetime import datetime, timezone

base = Path('/home/dombarker/project-offloads')
old = base/'aspis-r1-r18-sampler-rank-20261016'
w = base/'aspis-r1-r18-sampler-rank-consumers-20261016'
w.mkdir(exist_ok=True)
shutil.copy2(old/'runner.py',w/'runner.py')
spec=importlib.util.spec_from_file_location('runner',w/'runner.py')
r=importlib.util.module_from_spec(spec);spec.loader.exec_module(r)
snapshot=old/'external-inputs-rank.json'
data,_=r.verify_snapshot(snapshot)
manifest=json.loads((old/'sources/SOURCE-MANIFEST.json').read_text())
basekeys=r.external_keys(data)
names=['R1SamplerBlockRank','AspisR72Sampler.Types','AspisR72Sampler.Funs']
mixed='AspisV8R19.SamplerWordRead'
failed=old/'runs/rank-chain-a'/mixed
rootrecords=[{'name':'rank_checked','source':str(old/'sources'),'objects':str(old/'objects')},
    {'name':'rank_mixed','source':str(old/'sources'),'objects':str(failed/'artifacts')}]
data['roots']=rootrecords+data['roots']
records={}
for name in names+[mixed]:
    src=old/'sources'/manifest['modules'][name]['stage_as']
    rp=(failed/'receipt.json') if name==mixed else old/'successful-targets'/(name+'.json')
    receipt=json.loads(rp.read_text())
    objectroot=(failed/'artifacts') if name==mixed else old/'objects'
    objects=r.object_pins(objectroot,name,data['olean_header_seal'])
    assert receipt['exit_status']==0
    assert receipt['key']['source_sha256']==r.sha(src)==manifest['modules'][name]['source_sha256']
    assert receipt['key']['runtime']==data['runtime_files']
    expected={}
    for dep in r.imports(src,implicit_init=True):
        if dep in records:
            dr=records[dep]
            expected[dep]={'receipt_key':r.digest(dr['key']), 'objects':r.object_pins(old/'objects',dep,data['olean_header_seal'])}
        else:
            expected[dep]={'objects':data['modules'][dep]['objects'],'closure_key':basekeys[dep]}
    assert receipt['key']['imports']==expected,name
    if name!=mixed:
        assert receipt['axioms']['passed'] and receipt['objects']==objects
    else:
        assert receipt['axioms']['passed'] is False
        reports=receipt['axioms']['reports']
        nonstandard={x['declaration']:{a for a in x['axioms'] if a not in r.STANDARD_AXIOMS} for x in reports}
        nonstandard={k:v for k,v in nonstandard.items() if v}
        assert nonstandard=={
            'AspisV8R19.SamplerWordRead.unwrap_success':{'core.fmt.Formatter'},
            'AspisV8R19.SamplerWordRead.read_success':{'core.fmt.Formatter'}}
    data['modules'][name]={'root':'rank_mixed' if name==mixed else 'rank_checked',
        'source':str(src),'source_sha256':r.sha(src),'imports':r.imports(src,implicit_init=True),
        'objects':objects,'build_receipt':{'path':str(rp),'sha256':r.sha(rp)}}
    if name==mixed:
        data['modules'][name]['mixed_axiom_scope']={
            'full_audit_passed':False,
            'excluded_declarations':list(nonstandard),
            'permitted_consumer_definition':'AspisV8R19.SamplerWordRead.four',
            'requirement':'Separate four/source_word/final rank/final actual sampler audits must be standard-only; no whole-module axiom claim.'}
    records[name]=receipt
data['provenance_files'][str(snapshot)]=r.sha(snapshot)
data['provenance_files'][str(old/'sources/SOURCE-MANIFEST.json')]=r.sha(old/'sources/SOURCE-MANIFEST.json')
data['scope']='Prior55 caches plus3 successful unchanged modules and1 explicit mixed-axiom module. SamplerWordRead compilation exited0 but full audit failed; read/unwrap remain excluded, no audit result relabeled and no Formatter allowance. Narrow consumer declarations require independent standard-only audits.'
data['captured_utc']=datetime.now(timezone.utc).isoformat()
r.external_keys(data);r.dump(w/'external-inputs-rank-consumers.json',data)
sources=w/'sources';sources.mkdir(exist_ok=True)
entries={}
pre='SamplerWordReadRankInterfaceAudit'
src=sources/(pre+'.lean')
src.write_text('import AspisV8R19.SamplerWordRead\n\n#print axioms AspisV8R19.SamplerWordRead.four\n')
entries[pre]={'source':'new audit-only target','source_sha256':r.sha(src),'source_revision':'834ae63ed267c7b8aa7031d2d7f7edaac591114c',
    'imports':r.imports(src),'stage_as':pre+'.lean','role':'Narrow audit of the only permitted mixed-module consumer definition'}
remaining=[name for name in manifest['topological_order'] if name not in names+[mixed,'SourceSamplerByteRankAudit']]
for name in remaining:
    item=manifest['modules'][name];src=old/'sources'/item['stage_as'];dest=sources/item['stage_as']
    dest.parent.mkdir(parents=True,exist_ok=True);shutil.copy2(src,dest);entries[name]=item
final='SourceSamplerByteRankAudit';src=sources/(final+'.lean')
src.write_text('import R1SourceSamplerByteRank\n\n#print axioms AspisV8R19.SamplerWordRead.four\n#print axioms AspisV8R19.SamplerWordBridge.source_word\n#print axioms AspisR1.SourceSamplerByteRank.word_value\n#print axioms AspisR1.SourceSamplerByteRank.run4_bytes\n#print axioms AspisR1.SourceSamplerByteRank.rank_lt\n')
entries[final]={'source':'new audit-only target','source_sha256':r.sha(src),'source_revision':'834ae63ed267c7b8aa7031d2d7f7edaac591114c',
    'imports':r.imports(src),'stage_as':final+'.lean','role':'Five exact standard-only consumer-cone checks; excludes old read/unwrap claims'}
r.dump(sources/'SOURCE-MANIFEST.json',{'format':2,'modules':entries,'topological_order':[pre]+remaining+[final],
    'groups':{'rank-consumers':{'targets':[pre,final]}}})
r.staged(w);r.verify_snapshot(w/'external-inputs-rank-consumers.json')
print(json.dumps({'targets':[pre]+remaining+[final],'snapshot_sha256':r.sha(w/'external-inputs-rank-consumers.json'),
    'source_manifest_sha256':r.sha(sources/'SOURCE-MANIFEST.json')},indent=2))
