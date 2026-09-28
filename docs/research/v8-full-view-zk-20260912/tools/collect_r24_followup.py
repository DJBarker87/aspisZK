#!/usr/bin/env python3
"""Compact source-locked follow-up evidence; omit keys, ELF and raw traces."""
import argparse,hashlib,json,shutil
from pathlib import Path
p=argparse.ArgumentParser();p.add_argument('--stage',action='append',default=[]);p.add_argument('--artifact',action='append',default=[]);p.add_argument('--output',type=Path,required=True)
p.add_argument('--base-revision',default='2ee34c1591fbdc6663fdb8529e559ba2eb14a675')
p.add_argument('--control',type=Path,default=Path('/home/dombarker/project-offloads/aspis-r20-compose-20260928-c'))
a=p.parse_args();out=a.output
assert not out.exists();out.mkdir()
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def copy(src,name):
    assert 'keypair' not in str(src)
    dst=out/name;dst.parent.mkdir(parents=True,exist_ok=True);shutil.copy2(src,dst)
def small_tree(src,label):
    for f in sorted(src.rglob('*')):
        if f.is_file() and f.suffix in ['.log','.json','.jsonl','.txt'] and 'keypair' not in f.name:
            copy(f,label+'/'+str(f.relative_to(src)))
summary={'source_base_revision':a.base_revision,'full_privacy_or_soundness_proved':False,'stages':{}}
control=a.control
for spec in a.stage:
    label,path=spec.split('=',1);s=Path(path);m=json.loads((s/'r18-stage.json').read_text())
    for n,h in m['files'].items():assert sha(s/n)==h,n
    copy(s/'r18-stage.json',label+'/r18-stage.json')
    info={'stage':path,'pins':len(m['files']),'manifest_sha256':sha(s/'r18-stage.json')}
    for d in ['host','sbf','svm','r24-host-a','r24-sbf-a','r24-svm-a','full-trace']:
        if(s/d).exists():small_tree(s/d,label+'/'+d)
    for n,h in m['files'].items():
        if (not(control/n).exists() or sha(control/n)!=h) and Path(n).suffix in ['.rs','.toml']:
            copy(s/n,label+'/source/'+n)
    receipt=s/'r24-svm-a/receipt.json'
    if receipt.exists():
        r=json.loads(receipt.read_text());assert r['source_manifest_sha256']==sha(s/'r18-stage.json')
        assert r['elf_sha256']==sha(s/'sbf-primary/aspis_v8_performance_sbf.so')
        for w in r['runs']:
            for x in w['results']:
                assert x['heap_bytes']==262144 and x['unchanged_accounts']
                if x['cu_limit']==100000000:assert x['accepted']if x['case']=='honest'else x['custom_rejection']and not x['resource_failure']
        info['full_cu']=[next(x['cu']for x in w['results']if x['cu_limit']==100000000 and x['case']=='honest')for w in r['runs']]
        info['one_million_accepted']=[next(x['accepted']for x in w['results']if x['cu_limit']==1000000 and x['case']=='honest')for w in r['runs']]
        checks=json.loads((s/'r24-host-a/wire-controls/results.json').read_text());assert len(checks['cases'])==3281 and sum(x['checked_rejection']for x in checks['cases'])==3280
        log=(s/'r24-sbf-a/compile.log').read_text();assert 'overflows the maximum allowed frame'not in log and not('Stack offset'in log and'exceeded'in log)
    summary['stages'][label]=info
for spec in a.artifact:
    label,path=spec.split('=',1);src=Path(path)
    if src.is_dir():small_tree(src,label)
    else:copy(src,label+'/'+src.name)
(out/'receipt.json').write_text(json.dumps(summary,indent=2)+'\n')
(out/'MANIFEST.json').write_text(json.dumps({str(f.relative_to(out)):sha(f)for f in sorted(out.rglob('*'))if f.is_file()},indent=2)+'\n')
print(json.dumps(summary,indent=2))
