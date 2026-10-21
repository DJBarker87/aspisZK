#!/usr/bin/env python3
"""Read-only receipt, source, axiom and scope audit; no compiler or solver."""
import hashlib
import json
from pathlib import Path
import re
import subprocess

ROOT=Path(__file__).resolve().parents[2]
PACKET=ROOT/'docs/research/100bit-spend-path-20261013'
EVIDENCE=PACKET/'evidence/dv-twotx-20261021'
def sha(p): return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def main():
    manifest=json.loads((EVIDENCE/'manifest.json').read_text())
    final={a['module']:a for a in manifest['attempts'] if a['final_current']}
    modules=sorted(list((PACKET/'lean').glob('OraclePortFrozen2*.lean'))+
                   list((PACKET/'lean').glob('Frozen2StartCharge*.lean'))+
                   list((PACKET/'lean').glob('OraclePortHeadlineFrozen2PerAttempt.lean')))
    report={'schema':'dv-twotx-audit-v1','modules':[], 'failed_attempts':[],
            'full_frozen_release_replay':False,'source_joins_discharged':False}
    for source in modules:
        baseline=subprocess.run(['git','cat-file','-e','27aa8ba07:'+str(source.relative_to(ROOT))],cwd=ROOT,stdout=subprocess.DEVNULL,stderr=subprocess.DEVNULL)
        assert baseline.returncode != 0, ('existing Lean source',source)
        a=final[source.stem]
        assert a['exit']==0 and a['source_sha256']==sha(source), source
        out=ROOT/a['log']
        assert json.loads((out.parent/'receipt.json').read_text())==a
        assert sha(out.parent/'source.lean.txt')==sha(source)
        log=out.read_text()
        assert not a['errors'] and 'error:' not in log
        for line in a['axioms']:
            if '[' in line:
                used=set(re.search(r'\[([\s\S]*?)\]',line)[1].replace('\n',' ').replace(' ','').split(','))
                assert used <= {'propext','Classical.choice','Quot.sound'},line
        code=source.read_text()
        assert not re.search(r'(?<![.\w])(sorry|admit|axiom|native_decide)\b|set_option\s+(maxRecDepth|maxHeartbeats)',re.sub(r'/-[\s\S]*?-/|--[^\n]*','',code))
        declared=re.findall(r'^(?:private\s+)?theorem\s+(\w+)',code,re.M)
        printed=re.findall(r'^#print axioms (\w+)',code,re.M)
        assert set(declared)<=set(printed),source
        assert len(a['axioms'])>=len(printed),(source,len(a['axioms']),len(printed))
        for dep in a['direct_imports']:
            assert sha(dep['path'])==dep['sha256'],dep
        report['modules'].append({'module':source.stem,'sha256':sha(source),'attempt':a['attempt'],
            'axiom_reports':len(a['axioms']),'exit':a['exit'],'wall_seconds':a['wall_seconds'],
            'peak_rss_bytes':a['peak_rss_bytes'],'swaps':a['swaps']})
    for a in manifest['attempts']:
        if a['exit']:
            report['failed_attempts'].append({'module':a['module'],'attempt':a['attempt'],'exit':a['exit'],'errors':a['errors']})
    paths=subprocess.check_output(['git','diff','--name-only','27aa8ba07'],cwd=ROOT,text=True).splitlines()
    for name in paths:
        assert not name.startswith(('crates/','programs/')) and '/lean-candidates/' not in name,name
        if '/lean/' in name:
            assert Path(name).stem.startswith(('OraclePortFrozen2','Frozen2StartCharge','OraclePortHeadlineFrozen2PerAttempt')),name
    for file in EVIDENCE.rglob('*.json'):
        assert file.stat().st_size<=5_000_000,file
    for filename,key in [('frozen-sources.json','sources'),('ordering-reuse.json','pins')]:
        pinfile=EVIDENCE/filename
        if pinfile.exists():
            for pin in json.loads(pinfile.read_text())[key]:
                assert sha(ROOT/pin['path'])==pin['sha256'],pin
                assert (ROOT/pin['path']).stat().st_size==pin['size'],pin
    report['axiom_reports']=sum(m['axiom_reports'] for m in report['modules'])
    report['peak_rss_bytes']=max(m['peak_rss_bytes'] for m in report['modules'])
    report['swaps']=sum(m['swaps'] for m in report['modules'])
    (EVIDENCE/'audit-summary.json').write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps({k:report[k] for k in ['axiom_reports','peak_rss_bytes','swaps']}))
if __name__=='__main__':main()
