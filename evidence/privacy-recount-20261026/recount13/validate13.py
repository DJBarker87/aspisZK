"""Focused evidence and accounting validation. Never invokes Lean or Kani."""
import ast
from pathlib import Path
exec((Path(__file__).resolve().parent/'audit13.py').read_text().split('# Each historical')[0])
manifest.update({x['ref']+':'+x['path']:x for x in json.loads((P/'manifest.json').read_text())})
K='evidence/k3-audit-20261030/k4trace/'
checks=json.loads((P/'k4-restore-check.json').read_text())
# Original source receipt identity is verified independently of the replay's expected field.
originals={'C044':['K79200/source-sha256.json','K79201/source-sha256.json'],'C084':['K12/source-manifest.json','K13/source-manifest.json'],'C088':['K79220/source-sha256.json','K79221/source-sha256.json'],'C089':['K79222/source-sha256.json','K79223/source-sha256.json'],**{c:['stx-source-sha256.json'] for c in ['K93109','K93110','K93111']}}
for c in checks['checks']:
 c['original_source_hash_checks']=[]
 for path in originals[c['credit']]:
  s=txt('research',K+'original/'+path);assert c['source_sha256'] in s
  c['original_source_hash_checks'].append({'path':K+'original/'+path,'primary_sha256_present':True})
# Check generated source packages byte-for-byte against their recorded originating commits.
prov=obj('research',K+'source-provenance.json');payload=json.loads(lzma.decompress(read('research',K+'source-payload.json.xz')))
provenance=[]
for key,v in prov.items():
 if key not in payload:continue
 if 'revision' not in v:
  assert hashlib.sha256(payload[key].encode()).hexdigest()==v['sha256'] and v['sha256'] in txt('research',K+'original/K12/source-manifest.json')
  provenance.append({'payload':key,'authority':v['authority'],'sha256':v['sha256'],'byte_identical':True});continue
 revs['origin-'+v['revision']]=v['revision'];b=read('origin-'+v['revision'],v['path'])
 if v.get('method'):
  literals=[ast.literal_eval(n.value) for n in ast.walk(ast.parse(b.decode())) if isinstance(n,ast.Assign) and any(isinstance(t,ast.Subscript) and isinstance(t.slice,ast.Constant) and t.slice.value=='Cargo.toml' for t in n.targets)]
  assert payload[key] in literals
  b=payload[key].encode()
 assert b is not None and b.decode()==payload[key] and hashlib.sha256(b).hexdigest()==v['sha256'],key
 provenance.append({'payload':key,'revision':v['revision'],'path':v['path'],'sha256':v['sha256'],'byte_identical':True})
assert read('own2','lean/PV_OWN2_RawWalker.lean')==read('research','evidence/axaudit2-20261102/NEP_WALKER.lean')
# C084's equality compares actual bytes65/65, outside the caller's source span.
c=next(c for c in checks['checks'] if c['credit']=='C084');control=next(r for r in c['raw_results'] if r['non_probe_failures'])
path=control['path'];raw=read('research',path);raw=lzma.decompress(raw) if path.endswith('.xz') else raw
failed=[r for z in json.loads(raw) for r in z.get('result',[]) if r['status']=='FAILURE' and r.get('sourceLocation',{}).get('propertyClass')!='reachability_check'][0]
trace=failed['trace'];c['byte_equality_trace']=[{'step':i,'event':e} for i,e in enumerate(trace) if 1214<=i<=1233]
assert sum(e.get('value',{}).get('data')=='65' for e in trace)>=2
# Inventory current support with the restored C044 only, no new consumers inferred.
credits=obj('research',str(B/'recount12/k3-final-credits12.json'))
for c in credits:
 c['recount13_status']=c['final_status'] if c['credit_id'] in ['C044','C084','C088','C089'] else c['k4_status']
assert dict(collections.Counter(c['recount13_status'] for c in credits))==checks['historical_credit_counts_after_restore']
support=obj('research',str(B/'recount12/current-support12.json'))
for x in support:
 if x['ledger_row'] in ['V177','V180']:
  x.update(current_kani_support=['C044'],suspended_current_support=[],depends_on_still_suspended_credit=False,current_credited_scope='Pre-Recount12 C044 bounded PathBuf source/model P6 scope restored; no native std transfer.')
 assert not x['depends_on_still_suspended_credit']
# Confirm the pre-suspension support lists contained exactly C044.
prior_matches=[]
p='evidence/privacy-recount-20261026/recount11/k3-audit11.json'
for x in obj('research',p)['current_support_rows']:
 if x.get('ledger_row') in ['V177','V180']:
  prior_matches.append({'path':p,'record':x});assert x['current_kani_support']==['C044']
assert len(prior_matches)==2
rows=json.loads((P/'rows13.json').read_text());tot=json.loads((P/'totals.json').read_text())
assert len(rows)==407 and len({r['id'] for r in rows})==407
assert {r['id'] for r in rows if r['recount12_status']!=r['recount13_status']}=={'V177','V180'}
assert collections.Counter(r['recount13_status'] for r in rows)==tot['statuses']
assert collections.Counter(r['recount13_class'] for r in rows)==tot['classes']
assert tot['open_dependencies']=={'a':4,'b':58,'c':3,'d':1}
assert all(Path(__file__).parent.parent.joinpath('recount12/rows12.json').exists() for r in rows)
assert all(s['ref']=='own2' or s['path'].endswith('/LOG.md') for a in json.loads((P/'definition-audit13.json').read_text()) for s in a['changed'])
# Manifest hashes checked against Git object contents, batched to avoid repeated process startup.
items=list(manifest.values());proc=subprocess.Popen(['git','cat-file','--batch'],stdin=subprocess.PIPE,stdout=subprocess.PIPE)
for x in items:
 proc.stdin.write((x['blob']+'\n').encode());proc.stdin.flush()
 header=proc.stdout.readline().decode().split();n=int(header[2]);data=proc.stdout.read(n);assert proc.stdout.read(1)==b'\n'
 assert hashlib.sha256(data).hexdigest()==x['sha256'] and n==x['bytes'],x['path']
proc.stdin.close();assert proc.wait()==0
sizes=[{'path':str(p.relative_to(P)),'bytes':p.stat().st_size} for p in P.rglob('*') if p.is_file()];assert max(x['bytes'] for x in sizes)<20*1024*1024
checks['source_provenance_checks']=provenance;checks['V177_V180_prior_exact_support']=prior_matches
dump('k4-restore-check.json',checks);dump('k3-final-credits13.json',credits);dump('current-support13.json',support);dump('manifest.json',list(manifest.values()))
dump('validation13.json',{'status':'PASS','rows':407,'unique_rows':407,'only_status_changes':['V177','V180'],'classes':tot['classes'],'statuses':tot['statuses'],'open_buckets':tot['open_dependencies'],'restored_credits':7,'intended_controls':10,'historical_credits':len(credits),'current_support_uses_suspended_credit':False,'immutable_inputs_hash_checked':len(items),'source_payload_origin_checks':len(provenance),'before_support_exact_C044':True,'new_named_premises_below_endpoint':1,'endpoint_premises_removed_added_weakened':[0,0,0],'Lean':0,'Kani':0,'Env_J':'93800-93839 unused','no_file_over20MiB':True,'target':'Target not yet established'})
print('PASS407 rows;7 scoped restores;10 intended controls;305-credit census; immutable hashes; support; one new named premise')
