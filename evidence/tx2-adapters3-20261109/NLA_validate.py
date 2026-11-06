from pathlib import Path
import json,lzma,hashlib,re,ast
E=Path(__file__).resolve().parent
sha=lambda b:hashlib.sha256(b).hexdigest()
rows=[json.loads(l) for l in (E/'NLA_ATTEMPTS.jsonl').read_text().splitlines()]
native=[r for r in rows if r['kind']=='kani'];assert len(native)==70
bad=['NLA_K001','NLA_K030'];positive=[];negative=[]
idx=json.loads((E/'NLA_INPUTS.json').read_text());stubs=set();features=[]
for r in native:
 a=r['attempt'];s=lzma.decompress((E/a/'stdout.log.xz').read_bytes()).decode()
 if a in bad:assert r['exit_status']==1 and 'could not compile' in s
 elif r['control']=='positive':
  assert r['exit_status']==0 and 'VERIFICATION:- SUCCESSFUL' in s,a;positive.append(a)
 else:
  assert r['control']=='inverse' and r['exit_status']==1 and 'VERIFICATION:- FAILED' in s and 'Failed Checks:' in s,a
  negative.append(a)
 g=json.loads((E/(a+'-graph-check.json')).read_text());assert g['graph_matches_frozen'] and not g['new_package_tuples'] and not g['edge_errors']
 assert {x[0] for x in g['missing_package_tuples']}=={'aspis-r1-cert-build','aspis-r1-cert-check','aspis-z4b-probe'}
 assert g['all_features'];features.append(dict(attempt=a,all_crates_features=a+'-graph-check.json',graph_sha256=g['graph_sha256']))
 lock=json.loads((E/(a+'-lock-check.json')).read_text());assert lock['unchanged'] and lock['before']==lock['after']==g['lock_sha256']
 erased=json.loads((E/(a+'-erasure-check.json')).read_text());assert erased['passed']
 source=json.loads((E/(a+'-source-check.json')).read_text());assert not source['errors']
 assert r['env']['CARGO_NET_OFFLINE']=='true' and r['env']['CARGO_TARGET_DIR'].endswith('/codex-cx-tx2-adapters3-20261109/NLA_target')
 for n,h in idx['attempts'][a].items():
  if n=='NLA_gate.py':
   gate=lzma.decompress((E/idx['objects'][h]['path']).read_bytes()).decode()
   tree=ast.parse(gate);kmx=next(ast.literal_eval(z.value) for z in tree.body if isinstance(z,ast.Assign) and any(isinstance(t,ast.Name) and t.id=='kmx' for t in z.targets))
   stubs.add(kmx['KMX_stubs.rs'])
assert len(positive)==len(negative)==34
assert len(stubs)==1,stubs
patch=E.parent/'kani-mitig-20261028/KMX_copy_stubs.patch'
for section in patch.read_text().split('diff --git ')[1:]:
 name=section.splitlines()[0].split(' b/',1)[1]
 raw=''.join(line[1:]+'\n' for line in section.splitlines() if line.startswith('+') and not line.startswith('+++'))
 assert name in kmx and sha(raw.encode())==kmx[name],name
for a in positive+negative:
 adm=json.loads((E/(a+'-admission.json')).read_text());assert adm['exit']==0 and adm['reservation']['allowed'] is True
 disk=json.loads((E/(a+'-disk-0.json')).read_text());assert disk['allowed'] and disk['free_bytes']>=40_000_000_000
current=['NLA_RootPrefix','NLA_LaneStep','NLA_DataPrefix','NLA_OwnedData','NLA_AllocationPrefix','NLA_PdaStatus','NLA_LaneAssemble']
for m in current:
 s=(E/(m+'.lean')).read_text();assert not re.search(r'\b(sorry|admit|native_decide|maxRecDepth|maxHeartbeats)\b',s)
 h=sha(s.encode());rs=[r for r in rows if r['module']==m and r['exit_status']==0 and h in r['source_hashes'].values()];assert rs,m
 log=lzma.decompress((E/rs[-1]['attempt']/'stdout.log.xz').read_bytes()).decode();assert 'sorryAx' not in log
 for theorem in re.findall(r'^theorem (\w+)',s,re.M):assert '#print axioms '+theorem in s
out=dict(native_invocations=70,positive=positive,matched_inverse=negative,matched_pairs=34,compile_failures=bad,retired_timeouts=[],memory_kills=[],quarantined=[],suspended=[],KMX_patch_sha256=sha(patch.read_bytes()),KMX_stub_source_sha256=next(iter(stubs)),features=features,frozen_lock_sha256='5782e6a32026fdd95d252d0db7ea20b16716e6deb4f5a397e744886bb6ba22ef',graph_note='All resolved tuples and edges match frozen lock; three unselected workspace helper packages omitted, no external-crate drift',current_modules=current,failed_drafts_excluded=['NLA_L002','NLA_L003','NLA_L006'],prelaunch_failure='NLA_L001_PRELAUNCH.json',shipped_source_changed=False,new_trust_rows=[],target_established=False,closed_rows=0)
(E/'NLA_VALIDATION.json').write_text(json.dumps(out,indent=1)+'\n')
print(json.dumps(dict(native=70,matched_pairs=34,current_lean_modules=len(current),graph_lock_source_erasure='PASS')))
