#!/usr/bin/env python3
"""Run explicit stages. Success of a code test is never reported as protocol certification."""
from __future__ import annotations
import argparse,json,os,subprocess,sys,time
from pathlib import Path
ROOT=Path(__file__).resolve().parent

def invoke(cmd,log):
    started=time.monotonic();p=subprocess.run(cmd,cwd=ROOT,text=True,capture_output=True)
    log.parent.mkdir(parents=True,exist_ok=True);log.write_text(p.stdout+p.stderr)
    print(p.stdout+p.stderr,end='')
    return {'exit':p.returncode,'seconds':time.monotonic()-started,'command':cmd,'log':str(log.relative_to(ROOT))}

if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--stage',choices=['python','static','preflight','lean','kernel','rust','all-local'],required=True)
    p.add_argument('--repo',type=Path);p.add_argument('--project',type=Path);p.add_argument('--build',type=Path)
    p.add_argument('--expected-version',default='4.32.2')
    a=p.parse_args();results={};stages=['python','static','rust'] if a.stage=='all-local' else [a.stage]
    for stage in stages:
        if stage=='python':cmd=[sys.executable,'-m','unittest','discover','-s','tests','-v']
        elif stage=='static':cmd=[sys.executable,'tools/source_audit.py','--out','results/source-inventory.json']
        elif stage=='preflight':
            if not a.repo:p.error('--repo is required')
            cmd=[sys.executable,'tools/reconcile.py','--repo',str(a.repo.resolve()),'--out',str(ROOT/'results/local-repair.json')]
        elif stage=='lean':
            if not a.project or not a.build:p.error('--project and fresh --build required')
            cmd=[sys.executable,'tools/lean_build.py','--project',str(a.project.resolve()),'--out',str(a.build.resolve()),'--expected-version',a.expected_version]
        elif stage=='kernel':
            if not a.project or not a.build:p.error('--project and --build required')
            cmd=[sys.executable,'tools/kernel_replay.py','--project',str(a.project.resolve()),'--build',str(a.build.resolve())]
        else:cmd=['cargo','test','--offline','--manifest-path',str(ROOT/'rust/Cargo.toml')]
        try:results[stage]=invoke(cmd,ROOT/'results'/f'{stage}-run.log')
        except OSError as e:
            results[stage]={'exit':2,'status':'NOT_RUN','reason':str(e)};print(stage+': NOT RUN: '+str(e),file=sys.stderr)
    (ROOT/'results/last-run.json').write_text(json.dumps(results,indent=2)+'\n')
    sys.exit(0 if all(r['exit']==0 for r in results.values()) else 1)
