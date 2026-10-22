#!/usr/bin/env python3
import hashlib, json, re, subprocess
from pathlib import Path
HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[4]
def sha(p): return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def req(ok,msg):
    if not ok: raise SystemExit('FAIL: '+msg)
m=json.loads((HERE/'manifest.json').read_text())
src=HERE/'sources/S4PrepareInstalledMeaningV1.lean'
req(sha(src)==m['source_sha256'],'target Lean source hash')
for name,info in m['direct_source_pins'].items():
    p=HERE/'source-pins'/name
    req(p.is_file() and sha(p)==info['sha256'],f'direct source pin {name}')
for name,info in m['selected_olean_owners'].items():
    p=Path(info['path'])
    req(p.exists() and sha(p)==info['sha256'],f'selected object owner {name}')
closure=json.loads((HERE/'proof/closure.json').read_text())
req(closure['modules']==6099 and closure['missing']==[],'import closure')
for mod,info in m['selected_olean_owners'].items():
    req(closure['owners'].get(mod,{}).get('sha256')==info['sha256'],f'closure owner {mod}')
r=json.loads((HERE/'proof/receipt.json').read_text())
req(r['exit_status']==0 and r['source_sha256']==m['source_sha256'],'successful compile receipt')
req(r['source_revision_at_launch']==m['source_revision_at_launch'],'launch revision pin')
req(r['object_sha256']==m['object_sha256'],'object receipt pin')
req(r['process_swaps']==0 and r['wall_seconds'] is not None and r['peak_process_rss_bytes']>0,'resource receipt')
cmd=json.loads((HERE/'proof/command.json').read_text())
req(cmd['argv'][-1]==str(src),'compile target argv')
req(cmd['argv'][cmd['argv'].index('-o')+1]==r['object_path_not_included'],'object output argv')
req(cmd['env']['LEAN_PATH_sha256']==r['lean_path_sha256'],'exact LEAN_PATH pin')
profile=(HERE/'proof/LEAN_PATH.txt').read_text().rstrip('\n')
req(hashlib.sha256(profile.encode()).hexdigest()==r['lean_path_sha256'],'exact LEAN_PATH profile contents')
log=(HERE/'proof/lean.log').read_text()
for t in [m['theorem']]:
    hits=re.findall(r"'AspisR1S4PrepareInstalledMeaningV1\.%s' depends on axioms: \[(.*?)\]"%re.escape(t),log,re.S)
    req(len(hits)==1,f'axiom report {t}')
    ax=set(re.findall(r'[A-Za-z][A-Za-z0-9_.]*',hits[0]))
    req(ax==set(m['accepted_axioms']),f'axiom set {t}: {sorted(ax)}')
text=src.read_text()
req(not re.search(r'(?m)^\s*(?:sorry|axiom)\b',text),'forbidden proof escape')
for p in HERE.rglob('*'):
    if p.is_file(): req(p.suffix not in {'.olean','.llbc','.bin'},f'compiled/binary artifact {p}')
parent=ROOT/'docs/research/100bit-spend-path-20261013/evidence/s4-candidate-prepare-s1-parent-v1-20261022/check-source-cut.py'
subprocess.run(['python3',str(parent)],check=True,stdout=subprocess.DEVNULL)
print('PASS: source pins, import owners, receipt, standard axioms, source-only policy, and parent source cut')
