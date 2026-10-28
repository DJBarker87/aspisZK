from pathlib import Path
import json,hashlib,subprocess,re
E=Path(__file__).resolve().parent
rows=[]
for p in sorted(E.glob('NBK_[LKG]*/receipt.json')):
 x=json.loads(p.read_text());a=p.parent.name
 assert x['limits']=={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'},(a,x['limits'])
 assert str(x['swaps'])=='0',(a,'swap')
 if x['kind']=='lean':
  assert '-M7000' in x['command'] and '-j1' in x['command']
  if x['exit_status']==0:
   for line in x['print_axioms']:
    assert 'sorryAx' not in line,line
    if 'depends on axioms:' in line:
     names=re.search(r'\[([^]]*)\]',line).group(1).replace(' ','').split(',')
     assert set(names)<={'propext','Classical.choice','Quot.sound'},line
 elif x['kind']=='kani':
  assert x['env']['CARGO_NET_OFFLINE']=='true' and x['env']['CARGO_PROFILE_DEV_OPT_LEVEL']=='3'
  assert '--locked' not in x['command']
  g=json.loads((E/(a+'-graph.json')).read_text())
  assert g['graph_matches_frozen'] and g['lock_unchanged'] and g['lock_before_sha256']==g['frozen_lock_sha256']==g['lock_after_sha256'],a
  assert (E/a.replace('_K','_G')/'receipt.json').exists()
 rows.append({k:x[k] for k in ['attempt','kind','module','source_revision','source_hashes','deps_fingerprint','command','exit_status','wall_seconds','peak_rss_kib','swaps','print_axioms','cgroup','limits']})
for p in Path('lean').glob('NBK_*.lean'):
 s=p.read_text()
 assert not re.search(r'\b(sorry|axiom|admit|native_decide)\b',s),p
 assert 'set_option maxHeartbeats' not in s and 'set_option maxRecDepth' not in s,p
 assert 'set_option autoImplicit false' in s or p.name=='NBK_Audit.lean',p
 own=[x for x in rows if x['kind']=='lean' and x['exit_status']==0 and p.name in x['command'][-1]]
 assert own,(p,'no passing compile')
 last=own[-1];h=hashlib.sha256(p.read_bytes()).hexdigest();assert h in last['source_hashes'].values(),(p,'unvalidated source change')
assert subprocess.run(['git','diff','--quiet','4bb3b3f51e16b4525f1d10336e2b0bcbbd775387','--','crates','programs']).returncode==0
summary={kind:{'attempts':sum(x['kind']==kind for x in rows),'passes':sum(x['kind']==kind and x['exit_status']==0 for x in rows)} for kind in ['lean','kani','metadata']}
assert summary['lean']['attempts']<=100 and summary['kani']['attempts']<=60
(E/'NBK_ATTEMPTS.jsonl').write_text(''.join(json.dumps(x)+'\n' for x in rows))
(E/'NBK_VALIDATION.json').write_text(json.dumps({'summary':summary,'current_modules_match_passing_sources':True,'standard_axioms_on_successes':True,'caps_verified':True,'worktree_crates_programs_frozen':True,'no_new_key_operations':True,'frozen_revision':'4bb3b3f51e16b4525f1d10336e2b0bcbbd775387','source_revision':subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),'not_a_full_release_replay':True},indent=2)+'\n')
print(json.dumps(summary))
