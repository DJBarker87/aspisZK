"""Read-only audit of focused S2Y receipts, limits, current sources and axioms."""
from pathlib import Path
import hashlib,json,re,subprocess
R=Path(__file__).resolve().parents[2]
D=R/'docs/research/100bit-spend-path-20261013';E=D/'evidence/s2y-20261023'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
inspection=json.loads((E/'inspection.json').read_text());base=inspection['base_revision']
standard={'propext','Classical.choice','Quot.sound'}
pattern=r"'([^']+)' (depends on axioms: \[([^\]]*)\]|does not depend on any axioms)"
final={'S2Y_ChildGeometry':3,'S2Y_OwnedChildren':4,'S2Y_ForestPublic':5,'S2Y_Audit':6}
receipts=[]
for p in sorted(E.glob('lean-*/receipt.json')):
 x=json.loads(p.read_text());log=(p.parent/'stdout.log').read_text()
 for name,h in x['source_hashes'].items():assert sha(p.parent/'sources'/name)==h
 assert x['limits']=={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'}
 reports=[]
 for theorem,report,used in re.findall(pattern,log,re.S):
  axioms={a.strip() for a in used.split(',') if a.strip()}
  if x['exit_status']==0:assert axioms<=standard,(p,theorem,axioms)
  reports.append({'theorem':theorem,'report':report,'axioms':sorted(axioms)})
 receipts.append({**x,'full_axioms':reports,'accepted':x['exit_status']==0,'errors':re.findall(r'^.*error:.*$',log,re.M)})
assert len(receipts)<=100
for mod,n in final.items():
 x=json.loads((E/f'lean-{n:03d}/receipt.json').read_text())
 assert x['exit_status']==0 and x['source_hashes'][mod+'.lean']==sha(D/'lean'/(mod+'.lean'))
 text=(D/'lean'/(mod+'.lean')).read_text()
 # New sources may explain missing premises in comments. Scan active lines.
 active=re.sub(r'/\-.*?\-/','',text,flags=re.S)
 assert not re.search(r'\b(sorry|admit|axiom|native_decide)\b|set_option\s+(maxRecDepth|maxHeartbeats)',active)
audit=next(x for x in receipts if x['attempt']=='lean-006')
assert len(audit['full_axioms'])==13
changed=subprocess.check_output(['git','diff','--name-only',base,'HEAD'],cwd=R,text=True).splitlines()
assert all(p.startswith(('docs/research/100bit-spend-path-20261013/lean/S2Y_','docs/research/100bit-spend-path-20261013/design/S2Y-','docs/research/100bit-spend-path-20261013/evidence/s2y-','tools/s2y-')) for p in changed),changed
# All shipped files unchanged, not merely a selected three-file comparison.
assert not subprocess.check_output(['git','diff',base,'HEAD','--','programs','crates','Cargo.toml','Cargo.lock'],cwd=R)
manifest={'schema':'focused-extractor-proof-packet-v1','status':'conditional field ports; native S2 and release target not established','source_revision':subprocess.check_output(['git','rev-parse','HEAD'],cwd=R,text=True).strip(),'base_revision':base,'budgets':{'lean':100,'kani':60},'lean_attempts_used':len(receipts),'kani_runs_used':0,'preflight_failures_without_lean':1,'successful_attempts':sum(x['accepted'] for x in receipts),'final_modules':final,'final_axiom_reports':13,'final_axioms_standard_only':True,'max_peak_rss_kib':max(int(x['peak_rss_kib']) for x in receipts),'all_swaps_zero':all(x['swaps']=='0' for x in receipts),'shipped_source_changes':False,'scope':'one-module focused builds plus one axioms union audit; cached dependencies reused, not a coherent frozen manifest replay','receipts':receipts}
(E/'manifest.json').write_text(json.dumps(manifest,indent=2)+'\n')
print(json.dumps({k:manifest[k] for k in ['lean_attempts_used','kani_runs_used','successful_attempts','final_axiom_reports','max_peak_rss_kib','all_swaps_zero','shipped_source_changes']}))
