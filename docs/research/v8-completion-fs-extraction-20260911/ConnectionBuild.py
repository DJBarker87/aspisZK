#!/usr/bin/env python3
"""New source-connection leaves against the preceding clean certification.
Refuses stale imports, overwritten evidence, uncapped execution or tool changes.
"""
import argparse,hashlib,json,os,re,subprocess,sys,time
from pathlib import Path
ROOT=Path(__file__).resolve().parent
MODULES=['SameBodyPublicCorrection','SameBodyQueryClaim','SameBodyQueryFixtures',
         'FSTranscriptScript','SourceConnectionAudit']
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def main():
    p=argparse.ArgumentParser();p.add_argument('--work',type=Path,required=True);a=p.parse_args()
    assert sys.platform=='linux'
    group=next(x[3:] for x in Path('/proc/self/cgroup').read_text().splitlines() if x.startswith('0::'))
    scope=Path('/sys/fs/cgroup')/group.lstrip('/')
    limits={n:(scope/n).read_text().strip() for n in ['memory.high','memory.max','memory.swap.max']}
    assert limits['memory.swap.max']=='0'
    assert all(limits[n]!='max' and 0<int(limits[n])<=8*1024**3 for n in ['memory.high','memory.max'])
    before=json.loads((a.work/'build.json').read_text());fresh=json.loads((a.work/'freshness.json').read_text())
    assert before['status']==fresh['status']=='PASS'
    build=a.work/'artifacts';cwd=ROOT/'lean';available={'Std'}
    for f in before['files']:
        assert sha(cwd/(f['module']+'.lean'))==f['source_sha256']
        for name,digest in f['artifacts'].items():assert sha(build/name)==digest
        available.add(f['module'])
    assert sha(cwd/'FSFirstFresh.lean')==fresh['source_sha256']
    for name,digest in fresh['artifacts'].items():assert sha(build/name)==digest
    available.add('FSFirstFresh')
    version=subprocess.check_output(['lake','env','lean','--version'],cwd=cwd,text=True).strip()
    assert version==before['version']==fresh['version']
    prefix=Path(subprocess.check_output(['lake','env','lean','--print-prefix'],cwd=cwd,text=True).strip())
    assert sha(prefix/'bin/lean')==before['lean_binary_sha256']
    assert sha(prefix/'bin/leanchecker')==before['checker_binary_sha256']
    env=os.environ.copy();env['LEAN_PATH']=str(build.resolve())
    manifest=a.work/'connection.json';assert not manifest.exists()
    report={'version':version,'limits':limits,'prior_build_sha256':sha(a.work/'build.json'),
            'prior_freshness_sha256':sha(a.work/'freshness.json'),'files':[],'commands':[],
            'scope':'Five new source modules; eleven previous source-built modules hash-validated, not recompiled. Std reused. Same-kernel fresh replay, not external validation.'}
    def run(stage,command):
        log=a.work/'logs'/(stage+'.log');assert not log.exists();start=time.monotonic()
        with log.open('w') as out:
            result=subprocess.run(['/usr/bin/time','-v',*command],cwd=cwd,env=env,
                stdout=out,stderr=subprocess.STDOUT,timeout=540)
        item={'stage':stage,'command':command,'exit_code':result.returncode,
              'wall_seconds':time.monotonic()-start,'log_sha256':sha(log)}
        report['commands'].append(item);print(json.dumps(item),flush=True)
        return result.returncode==0
    passed=True
    for module in MODULES:
        src=cwd/(module+'.lean');digest=sha(src)
        imports=re.findall(r'^import\s+(\w+)',src.read_text(),re.M)
        assert all(i in available for i in imports)
        assert not (build/(module+'.olean')).exists()
        if not run(module+'-connection',['lake','env','lean','-j1','-M2048','-o',str(build/(module+'.olean')),str(src)]):
            passed=False;break
        assert sha(src)==digest
        report['files'].append({'module':module,'source_sha256':digest,'imports':imports,
            'artifacts':{p.name:sha(p) for p in build.glob(module+'.olean*')}})
        available.add(module)
    if passed:
        passed=run('SourceConnectionAudit-fresh',['lake','env',str(prefix/'bin/leanchecker'),'--fresh','-v','SourceConnectionAudit'])
    for f in report['files']:assert sha(cwd/(f['module']+'.lean'))==f['source_sha256']
    report['status']='PASS' if passed else 'FAIL'
    manifest.write_text(json.dumps(report,indent=2)+'\n')
    return 0 if passed else 1
if __name__=='__main__':
    try:raise SystemExit(main())
    except (AssertionError,OSError,subprocess.SubprocessError) as e:
        print('BLOCKED_OR_FAILED',e,file=sys.stderr);raise SystemExit(2)
