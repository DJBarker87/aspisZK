from pathlib import Path
import json,hashlib,re,subprocess
E=Path(__file__).resolve().parent;R=Path.cwd();rev='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387'
receipts=[json.loads(p.read_text()) for p in sorted(E.glob('NBN_*/receipt.json'))]
limits={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'}
for r in receipts:
 assert r['limits']==limits,r['attempt']
 assert r['swaps']=='0',r['attempt']
 if r['kind']=='lean':assert '-M7000' in r['command']
 if r['kind']=='kani':
  assert '--locked' not in r['command']
  assert r['env']['CARGO_NET_OFFLINE']=='true' and r['env']['CARGO_PROFILE_DEV_OPT_LEVEL']=='3'
  g=json.loads((E/(r['attempt']+'-graph.json')).read_text());assert g['graph_matches_frozen'] and g['lock_unchanged'] and g['lock_before_sha256']==g['lock_after_sha256']==g['frozen_lock_sha256']
 if r['kind']=='lean' and r['exit_status']==0:
  for line in r['print_axioms']:
   if 'depends on axioms:' in line:
    assert {a.strip() for a in line.split('[',1)[1].split(']',1)[0].split(',')}<={'propext','Classical.choice','Quot.sound'},line
current={}
for p in sorted(Path('lean').glob('NBN_*.lean')):
 h=hashlib.sha256(p.read_bytes()).hexdigest();good=[r for r in receipts if r['module']==p.stem and r['exit_status']==0 and h in r['source_hashes'].values()];assert good,p
 assert not re.search(r'\b(sorry|admit|native_decide)\b|^axiom\b|set_option (maxHeartbeats|maxRecDepth)',p.read_text(),re.M),p
 current[str(p)]=dict(sha256=h,accepted_attempt=good[-1]['attempt'])
audit=next(r for r in receipts if r['attempt']=='NBN_L100');assert audit['exit_status']==0 and len(audit['print_axioms'])==90
frozen=subprocess.run(['git','diff','--quiet',rev,'--','crates','programs']);assert frozen.returncode==0
# Evidence retains draft diagnostics, not draft Lean objects as deliverables.
assert not list(E.rglob('*.olean')) and not list(E.rglob('*.elf')) and not list(E.rglob('*.pyc'))
ledger=[]
for r in receipts:
 k=r['kind'];ledger.append({**{a:r[a] for a in ['attempt','module','kind','exit_status','wall_seconds','peak_rss_kib','swaps','source_revision','source_hashes','print_axioms']},'command':r['command'],'limits':r['limits'],'accepted_property':r['exit_status']==0,'native_P6_closure':False,'receipt':r['attempt']+'/receipt.json'})
(E/'NBN_ATTEMPTS.jsonl').write_text(''.join(json.dumps(r)+'\n' for r in ledger))
from collections import Counter
counts=Counter((r['kind'],r['exit_status']) for r in receipts)
result=dict(source_revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),current_modules=current,all_current_sources_accepted=True,axioms='90 final theorem prints; subsets of propext/Classical.choice/Quot.sound',final_audit={k:audit[k] for k in ['attempt','module','exit_status','wall_seconds','peak_rss_kib','swaps','source_revision']},attempt_counts={str(k):v for k,v in counts.items()},charged_lean_slots=100,actual_lean_invocations=99,charged_kani_slots=18,actual_kani_invocations=17,no_runs_after_L100=True,source_freeze=rev,crates_programs_byte_identical=True,elf_rebuild_trigger=False,full_manifest_release_claim=False,standard_caps_and_zero_swap=True,frozen_offline_optimized_kani=True,whole_native_members='OPEN; KDX fidelity and exact higher callback associations retained',no_new_stub=True)
(E/'NBN_VALIDATION.json').write_text(json.dumps(result,indent=2)+'\n')
print('Validated',len(current),'current modules and',len(receipts),'receipts; final theorem audit90; source freeze intact.')
