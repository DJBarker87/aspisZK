#!/usr/bin/env python3
"""Small Std-only source closure; no historical artifacts or network calls.
This is compilation/axiom evidence, not fresh kernel or source refinement.
"""
import argparse, hashlib, json, os, re, subprocess, tempfile
from pathlib import Path
from check import run

HERE = Path(__file__).resolve().parent
REPO = HERE.parents[2]
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
def main():
    p=argparse.ArgumentParser();p.add_argument('--root',required=True)
    args=p.parse_args();assert re.fullmatch(r'[A-Za-z][A-Za-z0-9_]*',args.root)
    sources=HERE/'lean';ordered=[];active=set()
    def visit(module):
        if module=='Std' or module in ordered:return
        assert module not in active,'cyclic dependency'
        active.add(module)
        path=sources/(module+'.lean');assert path.is_file()
        for line in path.read_text().splitlines():
            if line.startswith('import '):
                for imported in line.split()[1:]:
                    assert re.fullmatch(r'[A-Za-z][A-Za-z0-9_]*',imported)
                    visit(imported)
        active.remove(module);ordered.append(module)
    visit(args.root)
    out=REPO/'results'/HERE.name
    evidence=Path(tempfile.mkdtemp(prefix=args.root+'-',dir=out))
    report={'root':args.root,'revision':subprocess.check_output(['git','rev-parse','HEAD'],cwd=REPO,text=True).strip(),
            'scope':'Small first-party source closure; pinned Std distribution reused. Not fresh kernel replay.',
            'sources':{m:sha(sources/(m+'.lean')) for m in ordered},'commands':[]}
    report['version']=subprocess.check_output(['lake','env','lean','--version'],cwd=sources,text=True).strip()
    assert '4.33.1' in report['version']
    with tempfile.TemporaryDirectory(prefix='aspis-focused-leaf-') as work:
        env=os.environ.copy();env['LEAN_PATH']=work
        for m in ordered:
            item=run(m,['lake','env','lean','-j1','-M2048','-o',str(Path(work)/(m+'.olean')),m+'.lean'],sources,evidence,env)
            report['commands'].append(item)
            if item['exit_code']!=0:break
            assert sha(sources/(m+'.lean'))==report['sources'][m]
    passed=len(report['commands'])==len(ordered) and all(c['exit_code']==0 for c in report['commands'])
    report['status']='PASS' if passed else 'FAIL'
    (evidence/'report.json').write_text(json.dumps(report,indent=2)+'\n')
    print(evidence)
    return 0 if passed else 1
if __name__=='__main__':raise SystemExit(main())
