from pathlib import Path
import hashlib,json,re,subprocess
E=Path(__file__).resolve().parent;H='dombarker@100.108.41.90';B='/home/dombarker/project-offloads/codex-cx-leaf-p6-8-20261027';FROZEN='5782e6a32026fdd95d252d0db7ea20b16716e6deb4f5a397e744886bb6ba22ef'
errors=[];rows=[];allowed={'propext','Classical.choice','Quot.sound'}
for kind,count in [('L',60),('K',30)]:
 for i in range(1,count+1):
  a=f'LPh_{kind}{i:03}';r=json.loads((E/a/'receipt.json').read_text());ad=json.loads((E/(a+'-reservation.json')).read_text());cfg=json.loads((E/(a+'.json')).read_text())
  assert ad['allowed'] is True and (E/(a+'-barrier-0.log')).exists(),a
  assert r['limits']=={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'},a
  assert int(r['swaps'])==0 and r['source_revision'] and r['source_hashes'],a
  for k in ['source_revision','exit_status','wall_seconds','peak_rss_kib','swaps','cgroup_memory_peak_bytes','print_axioms']:assert k in r,(a,k)
  if kind=='L':
   data=(E/a/'source.lean.txt').read_bytes();assert hashlib.sha256(data).hexdigest() in r['source_hashes'].values(),a
   assert '-M7000' in r['command'] and r['command'].count('lean')==1,a
   if r['exit_status']==0:
    for line in r['print_axioms']:
     assert 'sorryAx' not in line,(a,line)
     if 'depends on axioms:' in line:
      names=set(line.split('depends on axioms: [')[1].rstrip(']').split(', '));assert names<=allowed,(a,names)
   status='PASS' if r['exit_status']==0 else 'FAILED'
  else:
   g=json.loads((E/(a+'-graph-check.json')).read_text());assert g['graph_matches_frozen'] and not g['new_package_tuples'] and not g['edge_errors'] and g['lock_sha256']==FROZEN,a
   assert (E/(a+'-lock-after.log')).read_text().split()[0]==FROZEN,a
   assert '--locked' not in r['command'] and r['env']['CARGO_NET_OFFLINE']=='true' and r['env']['CARGO_PROFILE_DEV_OPT_LEVEL']=='3',a
   assert '-Z' in r['command'] and 'stubbing' in r['command'],a
   assert r['source_hashes']['LPh_src/Cargo.lock']==FROZEN,a
   assert hashlib.sha256((E/(a+'-harness.patch')).read_bytes()).hexdigest()==json.loads((E/(a+'-patch.json')).read_text())['sha256'],a
   if r['exit_status']==0:status='PASS'
   elif i in [29,30]:status='DIAGNOSTIC_COUNTEREXAMPLE'
   else:
    log=(E/a/'stdout.log').read_text()
    status='TIMEOUT' if 'timed out' in log else 'UNWIND_FAILURE' if 'unwinding assertion' in log else 'COMPILE_FAILURE' if 'could not compile' in log else 'OTHER_FAILURE'
  rows.append({'attempt':a,'status':status,'exit':r['exit_status'],'wall_seconds':r['wall_seconds'],'peak_rss_kib':int(r['peak_rss_kib']),'swaps':int(r['swaps']),'source_revision':r['source_revision']})
# Reconstruct every per-run input from the retained exact patch and the read-only LPg final base.
basefiles=sorted({p.removeprefix('LPh_src/') for i in range(1,31) for p in json.loads((E/f'LPh_K{i:03}/receipt.json').read_text())['source_hashes']})
code='''from pathlib import Path
import json
B=Path('/home/dombarker/project-offloads/codex-cx-leaf-p6-7-20261027/LPg_src')
files='''+repr(basefiles)+'''
print(json.dumps({p:(B/p).read_text() if (B/p).exists() else None for p in files}))
'''
r=subprocess.run(['ssh',H,"python3 - <<'REMOTE'\n"+code+'\nREMOTE'],capture_output=True,text=True,check=True);base=json.loads(r.stdout)
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
checked=0
for i in range(1,31):
 a=f'LPh_K{i:03}';patches={}
 for part in re.split(r'(?=^--- )',(E/(a+'-harness.patch')).read_text(),flags=re.M):
  if not part:continue
  target=part.splitlines()[1].removeprefix('+++ b/');patches[target]=apply(base.get(target),part)
 for name,sha in json.loads((E/a/'receipt.json').read_text())['source_hashes'].items():
  p=name.removeprefix('LPh_src/');text=patches.get(p,base.get(p));assert text is not None,(a,p)
  assert hashlib.sha256(text.encode()).hexdigest()==sha,(a,p);checked+=1
ref=json.loads((E/'LPh_K030/full-stdout-reference.json').read_text())
r=subprocess.run(['ssh',H,'sha256sum '+B+'/LPh_K030/stdout.log'],capture_output=True,text=True,check=True);assert r.stdout.split()[0]==ref['sha256']
summary={}
for kind in ['L','K']:
 rr=[r for r in rows if r['attempt'].startswith('LPh_'+kind)];statuses={s:sum(r['status']==s for r in rr) for s in sorted({r['status'] for r in rr})}
 summary[kind]={'attempts':len(rr),'statuses':statuses,'wall_seconds':sum(r['wall_seconds'] for r in rr),'peak_rss_kib':max(r['peak_rss_kib'] for r in rr),'swaps':0}
out={'errors':errors,'budget':{'lean_used':60,'lean_limit':60,'kani_used':30,'kani_limit':30,'further_prover_runs':'FORBIDDEN under this allocation'},'summary':summary,'native_input_hashes_reconstructed':checked,'native_exact_patches':30,'tool_pins_match':json.loads((E/'LPh_toolchain.json').read_text())['matches_inherited_LPg'],'trace_K030_full_hash_verified_on_host':True,'scope_policy':'serial admitted 6G/8G/swap0/tasks64; Lean -M7000; optimized offline Kani; no raised timeout/cap','top_premises_removed':0,'rows':rows}
baseline='ed9cf10093c6a86cc044abb2c2f03889342fc54c'
authored=subprocess.run(['git','diff','--check',baseline,'--',str(E.relative_to(Path.cwd()))+'/*.lean',str(E.relative_to(Path.cwd()))+'/*.py',str(E.relative_to(Path.cwd()))+'/*.md',str(E.relative_to(Path.cwd()))+'/*.json'],capture_output=True,text=True)
assert authored.returncode==0,authored.stdout+authored.stderr
full=subprocess.run(['git','diff','--check',baseline],capture_output=True,text=True)
warned=re.findall(r'^(evidence/[^:]+):[0-9]+:',full.stdout,re.M)
assert all(name.endswith(('.log','.patch')) for name in warned),warned
out['whitespace_checks']={'authored_lean_python_markdown_json_exit':authored.returncode,'full_raw_evidence_exit':full.returncode,'raw_evidence_reason':'Verbatim compiler/solver logs and byte-exact unified-diff context retain original whitespace; these are not normalized or represented as source-code lint passes.','raw_warning_locations':len(warned)}
(E/'LPh_VERIFICATION.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps({k:v for k,v in out.items() if k!='rows'},indent=2))
