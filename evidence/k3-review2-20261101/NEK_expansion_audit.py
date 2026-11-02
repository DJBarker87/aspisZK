"""Close explicit added-module paths; never equate a missing include with frozen code."""
from NEK_scan import ROOT,E,read_json,sha,frozen,json,re,subprocess
from NEK_recover import recover
A=read_json(E/'NEK_SOURCE_AUDIT.json');out=[]
for item in A:
 if item['status']!='STORAGE_FREE_RECORDED_CLOSURE':continue
 rp=item['receipt'];o,missing=recover(rp);resolved=[];unknown=[]
 for inc in item['includes']:
  match=[n for n in o if n.endswith('/'+inc['path'])]
  if match:resolved.append(dict(include=inc,source=match,kind='exact recovered source'))
  else:
   rel=inc['source'].split('_src/',1)[-1];path=str(__import__('pathlib').Path(rel).parent/inc['path']);v=frozen(path)
   if v:resolved.append(dict(include=inc,source=path,sha256=sha(v),kind='frozen source; frozen storage inventory retained'))
   elif inc['path']=='r1_pool_adapter_original.rs':resolved.append(dict(include=inc,kind='inactive cfg(all(test,feature=pool-adapter)); Kani --lib without test cfg'))
   else:unknown.append(inc)
 fptr=[dict(source=n,line=i+1,text=l.strip()) for n,t in o.items() for i,l in enumerate(t.splitlines()) if re.search(r'Option\s*<\s*(?:unsafe\s+)?(?:extern\s+"[^"]+"\s+)?fn\s*\(',l)]
 status='OPEN' if unknown or missing or fptr else 'UNAFFECTED_EXPANDED'
 if 'NDN_K001/' in rp:status='OPEN'
 out.append(dict(receipt=rp,status=status,source_hashes=item['recovered_sources'],resolved_includes=resolved,unresolved_includes=unknown,unresolved_sources=missing,function_pointer_sites=fptr,reason='added module paths expanded; frozen modules and external dependency/macro/tool trust retained' if status!='OPEN' else 'needs receipt-specific expanded source or local-context migration'))
(E/'NEK_EXPANSION_AUDIT.json').write_text(json.dumps(out,indent=2)+'\n');print('expanded',len(out),'open',sum(r['status']=='OPEN' for r in out))
