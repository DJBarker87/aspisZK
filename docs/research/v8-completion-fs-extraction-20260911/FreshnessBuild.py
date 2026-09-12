#!/usr/bin/env python3
"""Focused new leaf + fresh replay against the already source-rebuilt closure.
No earlier source compilation is repeated and no historical Aspis cache used.
"""
import argparse,hashlib,json,os,subprocess,sys,time
from pathlib import Path
ROOT=Path(__file__).resolve().parent
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def main():
    p=argparse.ArgumentParser();p.add_argument('--work',type=Path,required=True);a=p.parse_args()
    assert sys.platform=='linux'
    group=next(x[3:] for x in Path('/proc/self/cgroup').read_text().splitlines() if x.startswith('0::'))
    scope=Path('/sys/fs/cgroup')/group.lstrip('/')
    limits={n:(scope/n).read_text().strip() for n in ['memory.high','memory.max','memory.swap.max']}
    assert limits['memory.swap.max']=='0'
    assert all(limits[n]!='max' and 0<int(limits[n])<=8*1024**3 for n in ['memory.high','memory.max'])
    before=json.loads((a.work/'build.json').read_text());assert before['status']=='PASS'
    build=a.work/'artifacts';cwd=ROOT/'lean'
    for f in before['files']:
        assert sha(cwd/(f['module']+'.lean'))==f['source_sha256']
        for name,digest in f['artifacts'].items():assert sha(build/name)==digest
    target='FSFirstFresh';source=cwd/(target+'.lean');source_hash=sha(source)
    assert source.read_text().splitlines()[0]=='import FSExposureOrder'
    assert not (build/(target+'.olean')).exists()
    version=subprocess.check_output(['lake','env','lean','--version'],cwd=cwd,text=True).strip()
    assert version==before['version']
    prefix=Path(subprocess.check_output(['lake','env','lean','--print-prefix'],cwd=cwd,text=True).strip())
    assert sha(prefix/'bin/lean')==before['lean_binary_sha256']
    assert sha(prefix/'bin/leanchecker')==before['checker_binary_sha256']
    env=os.environ.copy();env['LEAN_PATH']=str(build.resolve())
    report={'source_sha256':source_hash,'module':target,'version':version,'limits':limits,
            'previous_source_build_sha256':sha(a.work/'build.json'),'commands':[],
            'scope':'Only FSFirstFresh compiled; first-party imports validated against fresh source-build manifest. Fresh replay includes imports. Not external kernel.'}
    for stage,command in [('leaf',['lake','env','lean','-j1','-M2048','-o',str(build/(target+'.olean')),str(source)]),
                          ('fresh',['lake','env',str(prefix/'bin/leanchecker'),'--fresh','-v',target])]:
        log=a.work/'logs'/(target+'-'+stage+'.log');start=time.monotonic()
        with log.open('w') as out:
            result=subprocess.run(['/usr/bin/time','-v',*command],cwd=cwd,env=env,
                stdout=out,stderr=subprocess.STDOUT,timeout=540)
        item={'stage':stage,'command':command,'exit_code':result.returncode,
              'wall_seconds':time.monotonic()-start,'log_sha256':sha(log)}
        report['commands'].append(item);print(json.dumps(item),flush=True)
        if result.returncode:break
    assert sha(source)==source_hash
    report['artifacts']={p.name:sha(p) for p in build.glob(target+'.olean*')}
    okay=len(report['commands'])==2 and all(x['exit_code']==0 for x in report['commands'])
    report['status']='PASS' if okay else 'FAIL'
    (a.work/'freshness.json').write_text(json.dumps(report,indent=2)+'\n')
    return 0 if okay else 1
if __name__=='__main__':
    try:raise SystemExit(main())
    except (AssertionError,OSError,subprocess.SubprocessError) as e:
        print('BLOCKED_OR_FAILED',e,file=sys.stderr);raise SystemExit(2)
