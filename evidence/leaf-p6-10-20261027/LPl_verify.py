from pathlib import Path
import hashlib,json,re,subprocess
E=Path(__file__).resolve().parent;root=E.parent.parent
sha=lambda b:hashlib.sha256(b).hexdigest()
allowed={'propext','Classical.choice','Quot.sound'};rows=[];axes={};errors=[]
for kind,limit in [('L',80),('K',30)]:
 paths=sorted(E.glob('LPl_'+kind+'*/receipt.json'))
 assert len(paths)<=limit
 for p in paths:
  r=json.loads(p.read_text());a=r['attempt'];ad=json.loads((E/(a+'-reservation.json')).read_text())
  assert ad['allowed'] is True,a
  if (E/(a+'-admission.json')).exists():
   admission=json.loads((E/(a+'-admission.json')).read_text());assert admission['exit_status']==0 and admission['allowed'] is True,a
  assert r['limits']=={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'},a
  assert int(r['swaps'])==0 and r['source_revision'] and r['source_hashes'],a
  if kind=='L':
   assert '-M7000' in r['command'],a
   assert sha((p.parent/'source.lean.txt').read_bytes()) in r['source_hashes'].values(),a
   if r['exit_status']==0:
    for line in r['print_axioms']:
     assert 'sorryAx' not in line,(a,line)
     if 'depends on axioms:' in line:
      names=set(line.split('depends on axioms: [')[1].rstrip(']').split(', '));assert names<=allowed,(a,names)
     axes[line.split("'")[1]]=line
   status='PASS' if r['exit_status']==0 else 'FAILED_PROOF'
  else:
   g=json.loads((E/(a+'-graph-check.json')).read_text())
   assert g['graph_matches_frozen'] and not g['new_package_tuples'] and not g['edge_errors'],a
   assert g['lock_sha256']=='5782e6a32026fdd95d252d0db7ea20b16716e6deb4f5a397e744886bb6ba22ef',a
   assert (E/(a+'-lock-after.log')).read_text().split()[0]==g['lock_sha256'],a
   assert r['env']['CARGO_NET_OFFLINE']=='true' and r['env']['CARGO_PROFILE_DEV_OPT_LEVEL']=='3',a
   assert '--locked' not in r['command'],a
   assert sha((E/(a+'-harness.patch')).read_bytes())==json.loads((E/(a+'-patch.json')).read_text())['sha256'],a
   status='PASS' if r['exit_status']==0 else 'TIMEOUT' if 'timed out' in (p.parent/'stdout.log').read_text() else 'FAILED'
  rows.append(dict(attempt=a,status=status,exit=r['exit_status'],wall_seconds=r['wall_seconds'],peak_rss_kib=int(r['peak_rss_kib']),swaps=int(r['swaps']),revision=r['source_revision']))
# Reconstruct every actual native input using the frozen release plus the
# exact ordered inherited patches and each actual per-run owned patch.
mp=json.loads((root/'evidence/leaf-p6-3-20261027/LPc_INPUTS/LPc_input-map.json').read_text())
inherited=[root/'evidence/leaf-p6-1-20261027/LPa_kani_harness.patch',root/'evidence/leaf-p6-3-20261027/LPc_INPUTS'/mp['LPc_K020']['patch'],root/'evidence/leaf-p6-7-20261027/LPg_K030-harness.patch',root/'evidence/leaf-p6-8-20261027/LPh_K030-harness.patch']
patches=inherited+sorted(E.glob('LPl_K*-harness.patch'))
rels={p.removeprefix('LPl_src/') for r in rows if r['attempt'].startswith('LPl_K') for p in json.loads((E/r['attempt']/'receipt.json').read_text())['source_hashes']}
for p in patches:rels.update(re.findall(r'^\+\+\+ b/(.+)$',p.read_text(),re.M))
base={}
for rel in rels:
 p=subprocess.run(['git','show','4bb3b3f51e16b4525f1d10336e2b0bcbbd775387:'+rel],cwd=root,capture_output=True)
 base[rel]=p.stdout.decode() if p.returncode==0 else None

def apply(text,patch):
 lines=(text or '').splitlines(True);out=[];pos=0;parts=patch.splitlines(True);i=2
 while i<len(parts):
  m=re.match(r'@@ -(\d+)(?:,(\d+))? \+(\d+)(?:,(\d+))? @@',parts[i]);assert m,parts[i]
  at=int(m[1])-1 if int(m[1]) else 0;out+=lines[pos:at];pos=at;i+=1
  while i<len(parts) and not parts[i].startswith('@@ '):
   l=parts[i];i+=1
   if l.startswith('\\ No newline'):continue
   if l[0] in ' -':assert lines[pos]==l[1:],(lines[pos],l);pos+=1
   if l[0] in ' +':out.append(l[1:])
 out+=lines[pos:];return ''.join(out)

def patch(tree,p):
 for part in re.split(r'(?=^--- )',p.read_text(),flags=re.M):
  if not part.startswith('--- '):continue
  rel=part.splitlines()[1].removeprefix('+++ b/');tree[rel]=apply(tree.get(rel),part)
for p in inherited:patch(base,p)
checked=0
for row in rows:
 a=row['attempt']
 if not a.startswith('LPl_K'):continue
 tree=dict(base);patch(tree,E/(a+'-harness.patch'))
 for p,h in json.loads((E/a/'receipt.json').read_text())['source_hashes'].items():
  rel=p.removeprefix('LPl_src/');assert tree[rel] is not None and sha(tree[rel].encode())==h,(a,rel);checked+=1
summary={}
for k in ['L','K']:
 rr=[r for r in rows if r['attempt'].startswith('LPl_'+k)]
 summary[k]={'attempts':len(rr),'statuses':{s:sum(r['status']==s for r in rr) for s in sorted({r['status'] for r in rr})},'wall_seconds':sum(r['wall_seconds'] for r in rr),'peak_rss_kib':max(r['peak_rss_kib'] for r in rr),'swaps':0}
out={'errors':errors,'budget':{'lean_used':summary['L']['attempts'],'lean_limit':80,'kani_used':summary['K']['attempts'],'kani_limit':30,'exhausted':False},'summary':summary,'native_input_hashes_reconstructed':checked,'accepted_printed_names':len(axes),'axioms':axes,'scope_policy':{'limits':'6G high/8G max/swap0/tasks64; Lean-M7000; optimized offline Rust','one_scope_at_a_time_deviation':'L047 overlapped K013 for approximately1.218s; failed L047 excluded, exact journal retained; own launch guard repaired','all_other_launches':'sequential receipt collection; no shared infrastructure change'},'closed_leaves':['verifier::echeck (adopted domains0..2272)','compact::check_values (adopted464)','validate_record_fields (all rows,lengths0..3712)'],'first_open_leaf':'compact::expand_values: global native row-indexed write/frame relation; model induction/Result alone does not close it','headline':'AspisR1.RPx_Deployed.deployed','headline_premises_removed':0,'rows':rows}
(E/'LPl_VERIFICATION.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps({k:v for k,v in out.items() if k not in ['rows','axioms']},indent=2))
