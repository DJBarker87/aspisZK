"""Frozen body pins and conservative caller occurrence inventory; no credit promotion."""
from pathlib import Path
import json,subprocess,hashlib,re
E=Path(__file__).resolve().parent
x=json.loads((E.parent/'pool-inventory2-20261109/NKZ_INVENTORY.json').read_text());ids=[159,160,181,184,186,189,241,242,287,288,293,296,318,323,324,345,368,374,375,376,377,379,390,391]
sha=lambda s:hashlib.sha256(s.encode()).hexdigest();out=[];clauses={}
for row in ids:
 r=next(r for r in x['rows'] if r['id']=='POOL:'+str(row));p=r['source_file'];rev='b936275465600469312d1f058cdc91ea2a11f3dc' if p.startswith('programs/aspis-pool/') else '4bb3b3f51e16b4525f1d10336e2b0bcbbd775387';s=subprocess.check_output(['git','show',rev+':'+p],text=True);a,b=r['source_lines'];lines=s.splitlines()[a-1:b];lines[0]=lines[0].lstrip();fn='\n'.join(lines);body=fn[fn.index('{'):fn.rindex('}')+1]
 assert sha(fn)==r['full_function_sha256'],r['id'];assert sha(body)==r['frozen_body_sha256'],r['id']
 callers=[]
 for parent in x['rows']:
  for i,e in enumerate(parent.get('edges',[])):
   if r['function'] in e.get('targets',[]):callers.append(dict(parent_row=parent['id'],parent_function=parent['function'],occurrence=i,kind=e['kind'],line=e.get('line'),spelling=e.get('callee_spelling'),conservative=len(e.get('targets',[]))!=1))
 # The ledger retains all conservative caller edges, rather than deleting uncertain occurrences.
 if row==379:domain='PCG_SdkPda.Domain { seeds := seeds_with_bump, program := program_id }'
 elif row in [184,324]:domain='pending exact canonical-input domain from CLOSED shared callee at SAME arguments'
 else:domain='True (all well-typed own arguments; no added logical hypothesis)' if row in [159,160,181,186,241,242,287,288,323,345,368,374,375,376,377,390,391] else 'pending own-argument-only domain; row OPEN'
 clauses[r['id']]=dict(function=r['function'],domain_verbatim=domain,caller_occurrences=[dict(c,required_domain=domain,status='PARENT_MUST_DISCHARGE_AT_SAME_ARGUMENTS') for c in callers],status='OPEN_UNTIL_FINAL_STREAM_C_GATE')
 out.append(dict(row=r['id'],function=r['function'],source=p,revision=rev,source_lines=[a,b],full_function_sha256=sha(fn),frozen_body_sha256=sha(body),body=body,caller_occurrences=len(callers)))
(E/'PCG_SOURCE_MAP.json').write_text(json.dumps(out,indent=1)+'\n');(E/'PCG_CALLER_CLAUSES.json').write_text(json.dumps(clauses,indent=1)+'\n')
print('PCG24 frozen function/body hashes match; all conservative caller occurrences retained')
