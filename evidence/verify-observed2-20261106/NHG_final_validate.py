"""Final support-only checks; retain all prior CLOSED certificates verbatim."""
from pathlib import Path
import json,hashlib,subprocess,lzma,sys
sys.dont_write_bytecode=True
E=Path(__file__).resolve().parent;R=E.parent.parent
sha=lambda b:hashlib.sha256(b).hexdigest()
def read(n):return json.loads((E/n).read_text())
def old(n):return subprocess.check_output(['git','show',read('NHG_STAGE4_SEAL.json')['revision']+':'+str((E/n).relative_to(R))],cwd=R)
def validate():
 seal=read('NHG_STAGE4_SEAL.json');assert seal['revision'].startswith('4596cd288cd')
 for n,p in seal['files'].items():
  b=old(n);assert sha(b)==p['sha256']and len(b)==p['bytes']
 assert(E/'NHG_stage4_validate.py').read_bytes()==old('NHG_stage4_validate.py')
 assert(E/'NHG_CLOSED.json').read_bytes()==old('NHG_CLOSED.json')
 stage=read('NHG_STAGE4_VALIDATION.json');assert stage['status']=='PASS'and len(stage['new_rows'])==18
 tests=read('NHG_STAGE4_MUTATIONS.json');assert len(tests)==15 and all(x['rejected']for x in tests)
 for module,n in [('NHG_ClaimsDomain',87),('NHG_COMBINED_IMPORT',88)]:
  rc=read(f'NHG_L{n:03}/receipt.json');assert rc['exit_status']==0 and sha((E/(module+'.lean')).read_bytes())==rc['source_hashes']['NHG_generated/'+module+'.lean']
  assert all('sorryAx'not in line for line in rc['print_axioms'])
 raw=read('NHG_audit/batch11/proof11.json');assert raw['exit_status']==0 and len(raw['results'])==5
 assert {r['root']for r in raw['results']}==set(read('NHG_FINAL_ROOTS.json')['roots'])
 assert all(r['equal']and set(r['walked_axioms'])<={'propext','Classical.choice','Quot.sound'}for r in raw['results'])
 for n in [87,88,89,90]:assert read(f'NHG_L{n:03}/receipt.json')['exit_status']==0
 scan=list(map(json.loads,(E/'NHG_LOADED_scan.jsonl').read_text().splitlines()));assert len(scan)>=13558 and all(not r['dangling']and not r['duplicate_owners']and r['imports_match']for r in scan)
 attempts=list(map(json.loads,(E/'NHG_ATTEMPTS.jsonl').read_text().splitlines()));ids=[x['attempt']for x in attempts];assert len(set(ids))==len(ids)
 counts=dict(kani=sum(x['kind']=='kani'for x in attempts),lean_support=sum(x['kind']not in ['kani','extract']for x in attempts),extraction=sum(x['kind']=='extract'for x in attempts));assert counts==dict(kani=80,lean_support=90,extraction=1)
 export=read('NHG_EXPORT.json');assert export['formal_tool_invocations']==0 and export['cache_deleted']is False and export['loaded_modules']==len(scan)
 payload=lzma.decompress((E/'NHG_FINAL_CLOSURE_PINS.json.xz').read_bytes());assert sha(payload)==export['closure_sha256']==(E/'NHG_FINAL_CLOSURE_PINS.json.sha256').read_text().strip()
 closure=json.loads(payload);assert len(closure)==export['closure_objects']and any('/Aeneas/'in p for p in closure)
 assert all((x['bytes']>0 and len(x['sha256'])==64)for x in export['exported_files'].values())
 for n in ['NHG_Driver','NHG_ProofDriver']:
  pin=read('NHG_L090/'+n+'_BINARY_PIN.json');saved=export['exported_files']['bin/'+n]
  assert saved['sha256']==pin['sha256']and saved['bytes']==pin['bytes']
 result=dict(stage);result.update(final_status='PASS',budget_used=counts,total_NHG_raw_roots=112,final_support_raw_roots=5,scan_modules=len(scan),final_joint='NHG_L088',final_raw='NHG_L089',final_scan='NHG_L090',final_support_only=True,closed_rows_added_after_stage4=0,export_path=export['export_path'],exported_bytes=export['exported_bytes'],closure_objects=export['closure_objects'],claims129_closed=False,finish136_closed=False,verify_observed137_closed=False,source_to_elf_changed=False)
 return result
if __name__=='__main__':
 x=validate();(E/'NHG_LEDGER_DELTA.json').write_text(json.dumps(x,indent=1)+'\n');(E/'NHG_FINAL_VALIDATION.json').write_text(json.dumps(x,indent=1)+'\n');print(json.dumps({k:x[k]for k in ['final_status','new_rows','budget_used','total_NHG_raw_roots','scan_modules','verify_observed137_closed']}))
