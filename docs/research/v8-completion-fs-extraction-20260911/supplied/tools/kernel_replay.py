#!/usr/bin/env python3
"""Replay a built pack root, when the matching checker exists. Never silently skip."""
from __future__ import annotations
import argparse,hashlib,json,os,shutil,subprocess,sys
from pathlib import Path

if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--project',type=Path,required=True);p.add_argument('--build',type=Path,required=True)
    p.add_argument('--timeout',type=int,default=1800);a=p.parse_args()
    try:
        report=json.loads((a.build/'build-report.json').read_text())
        if report['status']!='COMPILED_NOT_REPLAYED':raise RuntimeError('build is not all green')
        root=Path(__file__).resolve().parents[1]
        for item in report['files']:
            source=root/'lean'/Path(*item['module'].split('.')).with_suffix('.lean')
            output=a.build/Path(*item['module'].split('.')).with_suffix('.olean')
            if hashlib.sha256(source.read_bytes()).hexdigest()!=item['source_sha256']:raise RuntimeError('source changed after build')
            if hashlib.sha256(output.read_bytes()).hexdigest()!=item['olean_sha256']:raise RuntimeError('output changed after build')
        if not shutil.which('lake'):raise RuntimeError('lake absent')
        locate=subprocess.run(['lake','env','which','leanchecker'],cwd=a.project,text=True,capture_output=True)
        if locate.returncode:raise RuntimeError('matching leanchecker unavailable; inspect pinned toolchain, do not auto-install a different checker')
        checker=locate.stdout.strip()
        # LeanChecker ignores unknown flags, including --help. With no module
        # this can launch the default project's replay instead of showing help.
        prefix=subprocess.run(['lake','env','lean','--print-prefix'],cwd=a.project,
                              text=True,capture_output=True,check=True).stdout.strip()
        checker_source=Path(prefix)/'src'/'lean'/'LeanChecker.lean'
        text=checker_source.read_text()
        if 'let fresh := "--fresh" ∈ flags' not in text:
            raise RuntimeError('unreviewed checker CLI; inspect its exact pinned source')
        # A complete dependency replay belongs on the capped Linux runner.
        if not sys.platform.startswith('linux'):
            raise RuntimeError('fresh replay requires the authorised Linux cgroup runner')
        cgroups=Path('/proc/self/cgroup').read_text().splitlines()
        unified=next((line[3:] for line in cgroups if line.startswith('0::')),None)
        if unified is None:raise RuntimeError('cgroup v2 scope not found')
        scope=Path('/sys/fs/cgroup')/unified.lstrip('/')
        limits={name:(scope/name).read_text().strip() for name in
                ['memory.max','memory.high','memory.swap.max']}
        if limits['memory.swap.max']!='0' or any(limits[n]=='max' for n in ['memory.max','memory.high']):
            raise RuntimeError('finite MemoryHigh/MemoryMax and MemorySwapMax=0 required')
        env=os.environ.copy();env['LEAN_PATH']=str(a.build.resolve())+os.pathsep+report['external_lean_path']
        cmd=[checker,'--fresh','AspisV8Completion']
        result=subprocess.run(cmd,cwd=a.project,env=env,text=True,capture_output=True,timeout=a.timeout)
        (a.build/'kernel-replay.log').write_text(result.stdout+result.stderr)
        status={'status':'KERNEL_REPLAY_PASS' if result.returncode==0 else 'FAIL','command':cmd,
                'exit_code':result.returncode,'cgroup_limits':limits,
                'checker_source_sha256':hashlib.sha256(checker_source.read_bytes()).hexdigest(),
                'warning':'Same Lean kernel, not an independent external kernel or theorem-intent proof.'}
        (a.build/'kernel-replay.json').write_text(json.dumps(status,indent=2)+'\n')
        raise SystemExit(result.returncode)
    except (RuntimeError,OSError,ValueError,subprocess.TimeoutExpired) as e:
        print('BLOCKED:',e,file=sys.stderr);raise SystemExit(2)
