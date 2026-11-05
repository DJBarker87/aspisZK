from NIV_native import *
def packet(patch,module,parent,names):
 s=''.join(l[1:] for l in (E/patch).read_text().splitlines(True) if l.startswith('+') and not l.startswith('+++'));h=sha(s.encode())
 allrows=[json.loads(l) for l in (E/'NIV_ATTEMPTS.jsonl').read_text().splitlines()]
 for name in names:
  target='r1_pool_adapter::owned::'+module+'::'+name
  previous=[r for r in allrows if r['module']==target and h in r['source_hashes'].values()]
  if previous:
   assert len(previous)==1
   r=previous[0]
  else:
   i=next((i for i in range(1,121) if not (E/('NIV_K%03d.json'%i)).exists()),None);assert i,'Kani budget exhausted'
   r=fresh('NIV_K%03d'%i,target,[(parent,module,s)]);allrows.append(r)
  out=lzma.decompress((E/r['attempt']/'stdout.log.xz').read_bytes()).decode();expected=int(name.endswith('_wrong'))
  if r['exit_status']!=expected or ('VERIFICATION:- FAILED' if expected else 'VERIFICATION:- SUCCESSFUL') not in out:
   print('STOP_NATIVE_PACKET '+r['attempt'],flush=True);return False
 return True
if __name__=='__main__':
 phase=sys.argv[1]
 if phase=='sdk':packet('NIV_sdk.patch','NIV_sdk','programs/r1-cost-probe/src/r1_pool_adapter_owned.rs',[prefix+str(i)+suffix for prefix,n in [('first',3),('second',7)] for i in range(n) for suffix in ['', '_wrong']])
 elif phase=='auth':packet('NIV_auth.patch','NIV_auth','programs/r1-cost-probe/src/r1_pool_adapter_owned.rs',[v+'_'+str(g)+suffix for v in ['v1','v2'] for g in range(10) for suffix in ['', '_wrong']])
