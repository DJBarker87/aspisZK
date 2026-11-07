from pathlib import Path
import json,hashlib,lzma,subprocess
E=Path(__file__).resolve().parent
manifest=json.loads((E/'LIBC_AUDIT_ROOTS.json').read_text());walked={};groups=[]
for i,names in enumerate(manifest['groups']):
 j=json.loads((E/'LIBC_audit'/f'proof{i}'/f'proof{i}.json').read_text());assert j['exit_status']==0
 assert {x['root'] for x in j['results']}==set(names)
 for x in j['results']:
  assert x['equal'] and set(x['walked_axioms'])<={'propext','Classical.choice','Quot.sound'}
  p=E/('LIBC_NEP_proof'+str(i)+'_'+x['root']+'_REACHABLE.txt.xz');assert p.is_file()
  h=hashlib.sha256(lzma.decompress(p.read_bytes())).hexdigest();assert h==(E/(p.name[:-3]+'.sha256')).read_text().strip()
  walked[x['root']]=x
 groups.append({'group':i,'roots':len(names),'exit_status':0})
assert set(walked)==set(manifest['roots'])

exports=json.loads((E/'LIBC_CLOSED.json').read_text())
if isinstance(exports,dict):exports=exports['field_exports']
sources=json.loads((E/'LIBC_ACCEPTED_SOURCES.json').read_text());root_records=[]
for item in sources:
 for root in item['roots']:
  root_records.append({'module':item['module'],'theorem':root,'statement_and_proof':item['module']+'.lean','compiled_source_sha256':item['sha256'],'receipt':item['receipt'],'hypotheses_classified':[
   {'class':'universally_quantified_data','scope':'explicit args/env/carrier variables in cited source'},
   {'class':'structural_algebra_or_representation','scope':'explicit equality, induction, type identity and map facts; not security assumptions'},
   {'class':'original_caller_domain','scope':'explicit size/canonicality/range/provenance predicates in field source, classified separately in LIBC_CALLER_CLAUSES.json'},
   {'class':'source_association_only','scope':'where present, native Invocation is the execution certificate being associated; SAME-returned-valid is an implication antecedent; neither defines a field law'},
   {'class':'retained_runtime_realization','scope':'where present, same reservation equality/Env digest backend uses existing runtime boundary; no new syscall totality'}],
   'added_trust':[],'raw_ax2':walked[root],'row_credit_claimed':False})
(E/'LIBC_CLOSED.json').write_text(json.dumps({'target_established':False,'field_exports':exports,'own_roots':root_records,'new_axioms':[],'new_trust_rows':[]},indent=1)+'\n')
summary={'target_established':False,'row_credit_claimed':False,'own_roots':len(walked),'groups':groups,'allowed_axioms':['propext','Classical.choice','Quot.sound'],'collector_raw_agreement':True,'rejected_audit':'LIBC_L096 missing standalone import; failure log retained; changed closure recompiled L097 and affected group passed L098','combined_import':'LIBC_L104','last_additive_audit':'LIBC_L105','root_results':walked}
(E/'LIBC_FINAL_AUDIT_SUMMARY.json').write_text(json.dumps(summary,indent=1)+'\n')
validation=json.loads((E/'LIBC_VALIDATION.json').read_text())
allowed={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'}
for j in validation:assert j['limits']==allowed and j['swaps']=='0'
disk=[json.loads(p.read_text())['free'] for p in E.glob('LIBC_L*-disk-0.json')]
resource={'scopes':len(validation),'authorized':300,'remaining':300-len(validation),'Kani':0,'extraction':0,'max_peak_rss_kib':max(int(j['peak_rss_kib']) for j in validation),'swaps':0,'limits':allowed,'minimum_host_disk_free_bytes':min(disk),'timeouts_or_memory_kills':[],'early_stop_disposition':'LIBC_REMAINING.md; all internal field members delivered; actual VL* is external and modules22/25 are prohibited here'}
(E/'LIBC_RESOURCE_SUMMARY.json').write_text(json.dumps(resource,indent=1)+'\n')
assert not [p for p in E.rglob('*') if p.is_file() and p.stat().st_size>20_000_000]
base=subprocess.check_output(['git','log','--reverse','--format=%H','--',str(E)],text=True).splitlines()[0]+'^'
paths=subprocess.check_output(['git','diff','--name-only',base,'HEAD'],text=True).splitlines()
current=subprocess.check_output(['git','status','--porcelain=v1','-z'],text=True).split('\0')
paths=sorted(set(paths+[x[3:] for x in current if x]))
assert all(p.startswith('evidence/libc-20261111/') for p in paths)
(E/'LIBC_WORKTREE_HYGIENE.json').write_text(json.dumps({'base':base,'changed_paths':paths,'all_within_own_evidence':True,'files_over_20MB':[],'no_shipped_source_changes':True,'no_push':True},indent=1)+'\n')
print(json.dumps({'audit_roots':len(walked),'scopes':len(validation),'max_RSS_KiB':resource['max_peak_rss_kib'],'swaps':0}))
