#!/usr/bin/env python3
"""Compile THIS PACK's first attempts in a new output root using a pinned existing project.

Does not claim a rebuild of all Aspis first-party dependencies. Use the
explicit import manifest to rebuild the actual promoted Aspis closure too.
"""
from __future__ import annotations
import argparse,hashlib,json,os,re,shutil,subprocess,sys,time
from pathlib import Path
sys.path.insert(0,str(Path(__file__).resolve().parent))
from import_manifest import manifest
from toolchain_policy import validation_permitted


def run(args):
    root=Path(__file__).resolve().parents[1];out=args.out.resolve()
    if out.exists() and any(out.iterdir()):raise RuntimeError('output root is not empty; choose a fresh directory')
    out.mkdir(parents=True,exist_ok=True)
    def project_cmd(argv):
        p=subprocess.run(argv,cwd=args.project,text=True,capture_output=True,timeout=args.timeout)
        if p.returncode:raise RuntimeError(p.stderr or p.stdout)
        return p.stdout.strip()
    if not shutil.which('lake'):raise RuntimeError('lake is unavailable: NOT RUN')
    lean=project_cmd(['lake','env','which','lean'])
    version=project_cmd([lean,'--version'])
    if f'version {args.expected_version},' not in version and f'version {args.expected_version})' not in version:
        raise RuntimeError('pinned Lean mismatch: '+version)
    if args.purpose=='validation' and not validation_permitted(version):
        raise RuntimeError('known opaque-value kernel issue: validation requires 4.32.2+ or separately reviewed patched toolchain; historical reproduction is not certification')
    base_path=project_cmd(['lake','env','printenv','LEAN_PATH'])
    env=os.environ.copy();env['LEAN_PATH']=str(out)+os.pathsep+base_path
    plan=manifest([root/'lean'],['AspisV8Completion'],['Mathlib','Init','Std','Lean'])
    if plan['status']!='RESOLVED_NOT_BUILT':raise RuntimeError('pack import closure unresolved')
    records=[];failed=set()
    for module in plan['topological_order']:
        entry=plan['modules'][module];source=Path(entry['path'])
        rel=Path(*module.split('.'));target=out/rel.with_suffix('.olean');target.parent.mkdir(parents=True,exist_ok=True)
        if any(dep in failed for dep in entry['imports']):
            records.append({'module':module,'status':'BLOCKED_DEPENDENCY'});failed.add(module);continue
        cmd=[lean,'-j1','-M9500','-R',str(root/'lean'),'-o',str(target),str(source)]
        started=time.monotonic()
        try:
            p=subprocess.run(cmd,cwd=args.project,env=env,text=True,capture_output=True,timeout=args.timeout)
            text=p.stdout+p.stderr;status='COMPILED' if p.returncode==0 else 'FAIL'
        except subprocess.TimeoutExpired as exc:
            text='TIMEOUT\n'+str(exc);status='TIMEOUT'
        log=out/rel.with_suffix('.log');log.write_text(text)
        if status=='COMPILED':
            audits=re.findall(r"depends on axioms:\s*\[([^]]*)\]",text)
            allowed={'propext','Classical.choice','Quot.sound'}
            if 'sorryAx' in text or any(set(re.findall(r'[A-Za-z_][A-Za-z0-9_.]*',a))-allowed for a in audits):
                status='AXIOM_FAIL'
        if status!='COMPILED':failed.add(module)
        records.append({'module':module,'status':status,'command':cmd,'seconds':time.monotonic()-started,
            'source_sha256':hashlib.sha256(source.read_bytes()).hexdigest(),
            'olean_sha256':hashlib.sha256(target.read_bytes()).hexdigest() if target.exists() else None,
            'log':str(log)})
    report={'status':('COMPILED_NOT_REPLAYED' if args.purpose=='validation' else 'HISTORICAL_COMPILE_ONLY') if not failed else 'FAIL','lean_version':version,
            'external_project':str(args.project.resolve()),'external_lean_path':base_path,
            'output':str(out),'files':records,'scope':'this pack only; Mathlib is an explicit external cache boundary'}
    (out/'build-report.json').write_text(json.dumps(report,indent=2)+'\n')
    return 1 if failed else 0

if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--project',type=Path,required=True);p.add_argument('--out',type=Path,required=True)
    p.add_argument('--expected-version',required=True);p.add_argument('--purpose',choices=['validation','historical'],default='validation');p.add_argument('--timeout',type=int,default=180)
    a=p.parse_args()
    try:raise SystemExit(run(a))
    except (RuntimeError,OSError,subprocess.TimeoutExpired) as e:
        print('BLOCKED:',e,file=sys.stderr);raise SystemExit(2)
