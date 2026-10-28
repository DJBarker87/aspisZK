from pathlib import Path
import hashlib,json,re,subprocess
E=Path(__file__).resolve().parent;R=E.parents[1];D=R/'docs/research/100bit-spend-path-20261013/lean'
sha=lambda b:hashlib.sha256(b).hexdigest()
rows=json.loads((E/'NBJ_ATTEMPTS.json').read_text())['rows'];kani=[x for x in rows if x['kind']=='kani'];lean=[x for x in rows if x['kind']=='lean']
assert len(kani)==50 and len(lean)<=100
versions={}
for p in E.glob('NBJ_harness*.patch'):
 subprocess.run(['git','apply','--check',str(p)],cwd=R,check=True)
 name=None;lines=[]
 for l in p.read_text().splitlines(True)+['--- END\n']:
  if l.startswith('--- '):
   if name and name.endswith(('NBJ_keys.rs','NBJ_multiproof.rs')):versions.setdefault(name,set()).add(sha(''.join(lines).encode()))
   name=None;lines=[]
  elif l.startswith('+++ b/'):name=l[6:].strip()
  elif name and l.startswith('+'):lines.append(l[1:])
lean_hashes={sha(p.read_bytes()) for p in D.glob('NBJ_*.lean')}|{sha(p.read_bytes()) for p in E.glob('NBJ_L*.source.lean.txt')}
for row in rows:
 a=row['attempt'];rc=json.loads((E/a/'receipt.json').read_text())
 assert rc['limits']=={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'}
 assert rc['swaps']=='0'
 assert json.loads((E/(a+'-reservation.json')).read_text())['allowed'] is True
 for name,digest in rc['source_hashes'].items():
  if name.endswith('.lean'):assert digest in lean_hashes,(a,name,'missing Lean snapshot')
  if name.endswith(('NBJ_keys.rs','NBJ_multiproof.rs')):assert digest in versions[name.removeprefix('NBJ_src/')],(a,name,'missing patch snapshot')
 if row['kind']=='kani':
  g=json.loads((E/(a+'-graph.json')).read_text())
  assert g['allowed'] and not g['new_packages'] and not g['edge_errors'] and g['unchanged']
  assert g['lock_before']==g['lock_after']=='5782e6a32026fdd95d252d0db7ea20b16716e6deb4f5a397e744886bb6ba22ef'
  assert g['resolved_packages']==441 and g['frozen_packages']==444
 elif row['kind']=='lean' and row['exit_status']==0:
  for line in rc['print_axioms']:
   names=line.split('axioms: [')[-1].rstrip(']').split(', ') if 'axioms: [' in line else []
   assert set(names)<={'propext','Classical.choice','Quot.sound'},(a,line)
fixture=json.loads((E/'NBJ_R001/receipt.json').read_text())
assert fixture['exit_status']==0
assert fixture['source_hashes']['NBJ_copy_native.rs']==sha((E/'NBJ_copy_native.rs.txt').read_bytes())
for p in D.glob('NBJ_*.lean'):
 assert not re.search(r'\b(sorry|admit|native_decide)\b|^\s*axiom\s|set_option\s+(maxHeartbeats|maxRecDepth)',p.read_text(),re.M),p
roots=re.findall(r'#print axioms (\S+)',(D/'NBJ_Audit.lean').read_text())
audits=[r for r in lean if r['command'][-1]=='NBJ_sources/NBJ_Audit.lean' and r['exit_status']==0]
assert len(audits)==1
assert {s.split("'")[1] for s in audits[0]['print_axioms']}==set(roots)
start=json.loads((E/'NBJ_INITIAL_HOST_PINS.json').read_text());end=json.loads((E/'NBJ_TERMINAL_HOST.json').read_text())
for g in ['cache','coherent','aeneas']:assert all(end[g].get(p)==v for p,v in start[g].items()),g
assert end['frozen_sources_equal'] and end['frozen_source_files']==498 and not end['live_owned_builds'] and not end['private_objects']
base='79bf6326f9^'
changed=subprocess.check_output(['git','diff','--name-only',base,'--'],cwd=R,text=True).splitlines()
assert all(n.startswith('evidence/native-tx1c-20261027/') or n.startswith('docs/research/100bit-spend-path-20261013/lean/NBJ_') for n in changed),changed
out=dict(all_checks_passed=True,kani_runs=50,kani_passes=sum(r['exit_status']==0 for r in kani),kani_timeouts=sum(r['timeout'] for r in kani),lean_attempts=len(lean),lean_passes=sum(r['exit_status']==0 for r in lean),accepted_top_roots=len(roots),source_snapshots_retained=True,patches_apply=True,all_graphs_frozen=True,all_accepted_axioms_standard=True,frozen_source_files=498,shipped_files_unchanged=True,persistent_cache_retained=True,initial_objects_unchanged={g:len(start[g]) for g in ['cache','coherent','aeneas']},scheduling_exception='NBJ_SCOPE_EXCEPTION.md; K001/L001 overlap, not all attempts serial',max_rss_kib=max(int(x['peak_rss_kib']) for x in rows),total_wall_seconds=sum(x['wall_seconds'] for x in rows))
(E/'NBJ_STATIC_VALIDATION.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))
