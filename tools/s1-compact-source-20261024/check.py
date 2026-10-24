#!/usr/bin/env python3
"""Check the source-only circle/native-compact focused packet; never run Lean."""
from pathlib import Path
import hashlib,json,re,subprocess,sys
R=Path(__file__).resolve().parents[2]
B=R/'docs/research/100bit-spend-path-20261013'
S=B/'lean-candidates/s126-caller-boundary-20261021'
E=B/'evidence/s126-current-caller-20261021'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
subprocess.run([sys.executable,str(Path(__file__).with_name('adapt-native.py')),'--check'],check=True)
m=json.loads((E/'s1-circle-compact-targets.json').read_text())
receipts={}
for n,rel in m['targets'].items():
 r=json.loads((E/rel).read_text());receipts[n]=r
 assert r['target']==n and r['exit_status']==0 and r['swaps']==0,n
 assert sha(S/(n+'.lean'))==r['source_sha256'],n
 assert r['print_axioms'] and not any('sorryAx' in x or 'axioms: [' in x and any(t not in {'propext','Classical.choice','Quot.sound'} for t in re.search(r'axioms: \[(.*?)\]',x,re.S)[1].replace('\n',' ').replace(' ','').split(',')) for x in r['print_axioms']),n
 source=(S/(n+'.lean')).read_text()
 assert not re.search(r'\b(sorry|axiom|native_decide|bv_decide)\b|set_option\s+(maxHeartbeats|maxRecDepth)',source),n
for n,r in receipts.items():
 for imp,owner in r['direct_imports'].items():
  if imp in receipts:assert owner['sha256']==receipts[imp]['object_sha256'],(n,imp,'changed import owner needs focused recheck')
for f,expected in m['files'].items():assert sha(R/f)==expected,f
for p in (E/'s1-native-compact-extraction').rglob('*'):
 if p.is_file():assert p.suffix in {'.json','.log','.txt'},p
reuse=E/'s1-circle-reused-source'
for f,expected in json.loads((reuse/'REUSE.json').read_text())['files'].items():assert sha(reuse/f)==expected,f
print(json.dumps({'targets':len(receipts),'wall_seconds':sum(r['wall_seconds'] for r in receipts.values()),'peak_rss_bytes':max(r['peak_rss_bytes'] for r in receipts.values()),'swaps':0,'qualification':'Focused cached checks only. Native child/SDK/source joins and coherent release replay remain open.'}))
