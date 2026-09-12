#!/usr/bin/env python3
"""Clean first-party source rebuild and explicit-root fresh kernel replay.
Run in a dedicated finite-memory, zero-swap Linux cgroup; no fetches or caches
of first-party Aspis modules. Toolchain Std imports are reused and disclosed.
"""
import argparse, hashlib, json, os, re, subprocess, sys, time
from pathlib import Path

ROOT=Path(__file__).resolve().parent
MODULES=['CausalPrograms','SourceSqueeze','SemanticWireExecution','SameBodyRelation',
         'SameBodyOrdinary','SameBodyAssembly','FSOracleExecution','FSBoundedTranscript',
         'FSExposureOrder','CompletionSourceAudit']
def sha(path): return hashlib.sha256(path.read_bytes()).hexdigest()
def main():
    ap=argparse.ArgumentParser()
    ap.add_argument('--stage',choices=['build','replay'],required=True)
    ap.add_argument('--work',type=Path,required=True)
    args=ap.parse_args()
    if sys.platform!='linux': raise RuntimeError('Use the authorised capped Linux runner')
    group=next(x[3:] for x in Path('/proc/self/cgroup').read_text().splitlines() if x.startswith('0::'))
    scope=Path('/sys/fs/cgroup')/group.lstrip('/')
    limits={n:(scope/n).read_text().strip() for n in ['memory.high','memory.max','memory.swap.max']}
    assert limits['memory.swap.max']=='0'
    assert all(limits[n]!='max' and 0<int(limits[n])<=24*1024**3 for n in ['memory.high','memory.max'])
    args.work.mkdir(parents=True,exist_ok=True)
    build=args.work/'artifacts';build.mkdir(exist_ok=True)
    logs=args.work/'logs';logs.mkdir(exist_ok=True)
    cwd=ROOT/'lean'
    version=subprocess.check_output(['lake','env','lean','--version'],cwd=cwd,text=True).strip()
    assert '4.33.1' in version and '819816b2e0a3bf405af45ae5c7af2491d8f5bee6' in version
    prefix=Path(subprocess.check_output(['lake','env','lean','--print-prefix'],cwd=cwd,text=True).strip())
    env=os.environ.copy();env['LEAN_PATH']=str(build.resolve())
    report={'stage':args.stage,'version':version,'cgroup':group,'limits':limits,
        'lean_binary_sha256':sha(prefix/'bin/lean'),
        'checker_binary_sha256':sha(prefix/'bin/leanchecker'),
        'checker_source_sha256':sha(prefix/'src/lean/LeanChecker.lean'),
        'Std_import_sha256':sha(prefix/'lib/lean/Std.olean'),
        'scope':'New ten-module first-party closure only. Toolchain Std reused, not source rebuilt. Same Lean kernel, not independent external validation.',
        'files':[],'commands':[]}
    def run(name,command):
        start=time.monotonic()
        logfile=logs/(name+'.log')
        with logfile.open('w') as f:
            result=subprocess.run(['/usr/bin/time','-v',*command],cwd=cwd,env=env,
                stdout=f,stderr=subprocess.STDOUT,timeout=540)
        item={'name':name,'command':command,'exit_code':result.returncode,
              'wall_seconds':time.monotonic()-start,'log_sha256':sha(logfile)}
        report['commands'].append(item)
        print(json.dumps(item),flush=True)
        return result.returncode==0
    passed=True
    if args.stage=='build':
        if list(build.iterdir()): raise RuntimeError('Fresh build requires empty first-party artifact directory')
        for module in MODULES:
            src=cwd/(module+'.lean')
            imports=re.findall(r'^import\s+(\w+)',src.read_text(),re.M)
            assert all(i=='Std' or i in MODULES[:MODULES.index(module)] for i in imports)
            before=sha(src)
            if not run(module,['lake','env','lean','-j1','-M2048','-o',str(build/(module+'.olean')),str(src)]):
                passed=False;break
            assert sha(src)==before
            outputs={p.name:sha(p) for p in build.glob(module+'.olean*')}
            report['files'].append({'module':module,'source_sha256':before,'imports':imports,'artifacts':outputs})
    else:
        prior=json.loads((args.work/'build.json').read_text())
        assert prior['status']=='PASS' and len(prior['files'])==len(MODULES)
        assert prior['lean_binary_sha256']==report['lean_binary_sha256']
        for file in prior['files']:
            assert sha(cwd/(file['module']+'.lean'))==file['source_sha256']
            for name,digest in file['artifacts'].items(): assert sha(build/name)==digest
        assert 'let fresh := "--fresh" ∈ flags' in (prefix/'src/lean/LeanChecker.lean').read_text()
        report['files']=prior['files']
        passed=run('fresh-kernel',['lake','env',str(prefix/'bin/leanchecker'),'--fresh','-v','CompletionSourceAudit'])
    report['status']='PASS' if passed else 'FAIL'
    (args.work/(args.stage+'.json')).write_text(json.dumps(report,indent=2)+'\n')
    return 0 if passed else 1
if __name__=='__main__':
    try: raise SystemExit(main())
    except (RuntimeError,AssertionError,OSError,subprocess.SubprocessError) as e:
        print('BLOCKED_OR_FAILED:',e,file=sys.stderr);raise SystemExit(2)
