#!/usr/bin/env python3
"""Focused historical-toolchain diagnostic. NEVER a clean certification.
Writes only a fresh output directory; historical overlay stays read-only.
"""
import argparse,hashlib,json,os,re,subprocess,sys,time
from pathlib import Path
def sha(p):
    h=hashlib.sha256()
    with p.open('rb') as f:
        for chunk in iter(lambda:f.read(1048576),b''):h.update(chunk)
    return h.hexdigest()
def main():
    p=argparse.ArgumentParser()
    for name in ['source','output','overlay','package','manifest','supplement']:p.add_argument('--'+name,type=Path,required=True)
    p.add_argument('--prior-leaf',type=Path,action='append',default=[],
                   help='Prior focused output directory; verify receipt, source and sole artifact before importing')
    a=p.parse_args();assert sys.platform=='linux'
    a.output.mkdir(exist_ok=False)
    group=next(x[3:] for x in Path('/proc/self/cgroup').read_text().splitlines() if x.startswith('0::'))
    limits={n:(Path('/sys/fs/cgroup')/group.lstrip('/')/n).read_text().strip()
            for n in ['memory.high','memory.max','memory.swap.max']}
    assert limits['memory.swap.max']=='0'
    assert all(limits[n]!='max' and 0<int(limits[n])<=10*1024**3 for n in ['memory.high','memory.max'])
    lake='/home/dombarker/.elan/bin/lake'
    oldpath=subprocess.check_output([lake,'env','printenv','LEAN_PATH'],cwd=a.package,text=True).strip()
    lean=subprocess.check_output([lake,'env','which','lean'],cwd=a.package,text=True).strip()
    version=subprocess.check_output([lean,'--version'],text=True).strip()
    assert '4.32.0' in version and '8c9756b28d64dab099da31a4c09229a9e6a2ef35' in version
    manifest=json.loads(a.manifest.read_text());checks=[]
    for f in manifest['files']:
        path=a.overlay/f['overlay'] if f.get('overlay') else Path(f['remote_cache'])
        actual=sha(path)
        checks.append({'module':f['module'],'kind':f['kind'],'path':str(path),'sha256':actual})
        assert actual==f['sha256'],str(path)
    restored=[]
    for line in a.supplement.read_text().splitlines():
        m=re.fullmatch(r'([0-9a-f]{64})\s+(.+)',line)
        if not m:continue
        path=Path(m[2]);assert path.parent==a.overlay
        assert sha(path)==m[1],str(path)
        restored.append({'path':str(path),'sha256':m[1]})
    assert len(restored)>=28
    sourcehash=sha(a.source)
    prior=[]
    for directory in a.prior_leaf:
        receipt=directory/'report.json'
        r=json.loads(receipt.read_text())
        assert r['status']=='PASS_LEAF_ONLY' and r['exit_code']==0
        assert r['version']==version
        assert r['manifest_sha256']==sha(a.manifest)
        assert r['supplement_sha256']==sha(a.supplement)
        original_source=Path(r['command'][-1])
        artifact=directory/(original_source.stem+'.olean')
        assert sha(original_source)==r['source_sha256'],str(original_source)
        assert sha(artifact)==r['artifact_sha256'],str(artifact)
        assert sha(directory/'compile.log')==r['log_sha256']
        assert sorted(str(x.relative_to(directory)) for x in directory.rglob('*.olean*'))==[artifact.name]
        # A chained consumer must explicitly revalidate every earlier leaf too.
        for dependency in r.get('prior_leaves_checked',[]):
            assert Path(dependency['directory']) in a.prior_leaf
            assert sha(Path(dependency['directory'])/'report.json')==dependency['receipt_sha256']
        prior.append({'directory':str(directory),'receipt_sha256':sha(receipt),
                      'source':str(original_source),'source_sha256':sha(original_source),
                      'artifact':str(artifact),'artifact_sha256':sha(artifact)})
    report={'status':'RUNNING','version':version,'limits':limits,'source_sha256':sourcehash,
      'manifest_sha256':sha(a.manifest),'recorded_imports_checked':checks,
      'prior_leaves_checked':prior,
      'supplement_sha256':sha(a.supplement),'post_run_observation_imports_checked':restored,
      'scope':'Historical cached-import leaf only. Supplement is post-run observation, not an original compilation receipt. No clean dependency rebuild. Patched rebuild and fresh replay NOT RUN.'}
    output=a.output/(a.source.stem+'.olean')
    command=[lean,'-j1','-M9000','-R',str(a.source.parent),'-o',str(output),str(a.source)]
    env=os.environ.copy();env['LEAN_PATH']=':'.join([str(a.output),*(str(x) for x in a.prior_leaf),str(a.overlay),oldpath])
    report['command']=command;report['lean_path']=env['LEAN_PATH'];start=time.monotonic()
    with (a.output/'compile.log').open('w') as f:
        result=subprocess.run(['/usr/bin/time','-v',*command],cwd=a.package,env=env,stdout=f,stderr=subprocess.STDOUT,timeout=540)
    report.update(exit_code=result.returncode,wall_seconds=time.monotonic()-start,
      log_sha256=sha(a.output/'compile.log'),status='PASS_LEAF_ONLY' if result.returncode==0 else 'FAIL')
    assert sha(a.source)==sourcehash
    for entry in checks+restored:
        assert sha(Path(entry['path']))==entry['sha256'],entry['path']
    for entry in prior:
        assert sha(Path(entry['source']))==entry['source_sha256']
        assert sha(Path(entry['artifact']))==entry['artifact_sha256']
        assert sha(Path(entry['directory'])/'report.json')==entry['receipt_sha256']
    report['postflight_import_hashes_unchanged']=True
    if output.exists():report['artifact_sha256']=sha(output)
    (a.output/'report.json').write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps({k:v for k,v in report.items() if k not in ['recorded_imports_checked','lean_path']}),flush=True)
    return 0 if result.returncode==0 else 1
if __name__=='__main__':raise SystemExit(main())
