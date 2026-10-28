from pathlib import Path
import json,hashlib,subprocess,re
E=Path(__file__).resolve().parent
accepted={'NBD_DigestInduction':'NBD_L004','NBD_DigestTrace':'NBD_L008','NBD_DigestNativeStep':'NBD_L012','NBD_TerminalProjection':'NBD_L013','NBD_Audit':'NBD_L014'}
modules={}
for name,attempt in accepted.items():
 p=Path('lean')/(name+'.lean');rc=json.loads((E/attempt/'receipt.json').read_text());sha=hashlib.sha256(p.read_bytes()).hexdigest()
 assert rc['exit_status']==0 and sha in rc['source_hashes'].values(),name
 assert rc['print_axioms'] and all('sorryAx' not in s for s in rc['print_axioms'])
 assert not re.search(r'\b(sorry|axiom|admit|native_decide)\b|set_option\s+(maxRecDepth|maxHeartbeats)',p.read_text())
 assert 'XRn_' not in p.read_text()
 modules[name]=dict(attempt=attempt,sha256=sha,exit=rc['exit_status'],wall_seconds=rc['wall_seconds'],rss_kib=rc['peak_rss_kib'],swap=rc['swaps'],axioms=rc['print_axioms'])
receipts={}
for pattern in ['NBD_L*/receipt.json','NBD_K*/receipt.json','NBD_G*/receipt.json']:
 for p in E.glob(pattern):
  r=json.loads(p.read_text());assert r['limits']=={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'}
  receipts[r['attempt']]={k:r[k] for k in ['kind','module','exit_status','wall_seconds','peak_rss_kib','swaps','source_revision','source_hashes','print_axioms']}
for a in ['NBD_K003','NBD_K004','NBD_K005','NBD_K006','NBD_K008','NBD_K009']:
 q=json.loads((E/(a+'-graph.json')).read_text());assert q['graph_matches_frozen'] and q['lock_unchanged'] and q['lock_before_sha256']==q['lock_after_sha256']==q['frozen_lock_sha256']
 for field in ['frozen_lock_sha256']:assert q[field]==hashlib.sha256(subprocess.check_output(['git','show','4bb3b3f51e16b4525f1d10336e2b0bcbbd775387:Cargo.lock'])).hexdigest()
# No new forbidden shipped-file change, including cfg(kani) modules in this worktree.
base=subprocess.check_output(['git','rev-parse','05e202930b^'],text=True).strip()
changed=subprocess.check_output(['git','diff','--name-only',base,'HEAD'],text=True).splitlines()
assert all(p.startswith('evidence/native-tx2b-20261027/') or p.startswith('lean/NBD_') for p in changed)
source_trees={}
for name in ['crates','programs']:
 tip=subprocess.check_output(['git','rev-parse','HEAD:'+name],text=True).strip();frozen=subprocess.check_output(['git','rev-parse','4bb3b3f51e16b4525f1d10336e2b0bcbbd775387:'+name],text=True).strip();assert tip==frozen,(name,tip,frozen);source_trees[name]=dict(current=tip,frozen=frozen,identical=True)
start=json.loads((E/'NBD_CACHE_START.json').read_text());end=json.loads((E/'NBD_CACHE_END.json').read_text())
changed_cache=[p for p in start if p in end and start[p]!=end[p]]
assert not [p for p in changed_cache if Path(p).name.startswith('NBD_')],changed_cache
summary=dict(status='U03/U04/U05 OPEN; five local member bridges CLOSED; 43 exact open members',lean_used=sum(r['kind']=='lean' for r in receipts.values()),lean_budget=100,kani_invocations=sum(r['kind']=='kani' for r in receipts.values()),kani_budget=30,metadata_receipted=sum(r['kind']=='metadata' for r in receipts.values()),unreceipted_preproof_scope='NBD_G007: source snapshot failed on missing own file before cargo; never resubmitted',modules=modules,receipts=receipts,source_trees=source_trees,cache_start_objects=len(start),cache_end_objects=len(end),cache_changed_existing_paths=changed_cache,cache_missing_start_paths=sorted(set(start)-set(end)),artifact_scope='No shipped/cfg(kani) worktree changes; no ELF rebuild triggered; historical pins only',headline_premises_removed=0,assumptions_changed=0)
assert summary['lean_used']<=100 and summary['kani_invocations']<=30
(E/'NBD_VALIDATION.json').write_text(json.dumps(summary,indent=2)+'\n')
(E/'NBD_ATTEMPTS.jsonl').write_text(''.join(json.dumps(dict(attempt=a,**r))+'\n' for a,r in sorted(receipts.items())))
print({k:summary[k] for k in ['status','lean_used','kani_invocations','metadata_receipted']})
