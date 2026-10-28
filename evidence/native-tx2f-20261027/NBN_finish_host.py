from pathlib import Path
import subprocess,json,hashlib,time
E=Path(__file__).resolve().parent;H='dombarker@100.108.41.90';B='/home/dombarker/project-offloads/codex-cx-native-tx2f-20261027';cache='/home/dombarker/project-offloads/codex-cx-leaf-cache-20261027'
leanpath=json.loads((E/'NBN_L100/receipt.json').read_text())['env']['LEAN_PATH'].split(':')
pins=json.loads((E/'NBN_LIBRARY_PIN.json').read_text())
# Read-only audit; transport may be retried, never a prover submission.
script=f'''from pathlib import Path
import hashlib,json,subprocess
b=Path({B!r});c=Path({cache!r});roots={leanpath!r};pins={pins!r}
def pin(p):return dict(sha256=hashlib.sha256(p.read_bytes()).hexdigest(),bytes=p.stat().st_size)
objects={{str(p.relative_to(c)):pin(p) for p in c.rglob('*') if p.is_file()}}
resolved={{}}
for old,expected in pins.items():
 p=Path(old);rel='Aeneas.olean' if p.name=='Aeneas.olean' else 'Aeneas/'+str(p).split('/Aeneas/',1)[1]
 q=next((Path(r)/rel for r in roots if (Path(r)/rel).is_file()),None)
 assert q is not None,rel
 got=pin(q);assert got==expected,(q,got,expected)
 resolved[rel]=dict(path=str(q),**got)
ps=subprocess.check_output(['ps','-eo','pid,args'],text=True)
live=[l for l in ps.splitlines() if str(b) in l and any(x in l for x in ['cargo-kani kani','bin/lean ','cbmc ','S2W_run_host.py NBN_']) and 'python3 -' not in l]
assert not live,live
print(json.dumps(dict(cache=objects,resolved_aeneas=resolved,live_own_provers=live,persistent_cache_retained=str(c))))
'''
for n in range(11):
 r=subprocess.run(['ssh','-o','ConnectTimeout=15',H,'python3','-'],input=script,capture_output=True,text=True)
 if r.returncode!=255:break
 if n<10:time.sleep(60)
assert r.returncode==0,r.stderr
x=json.loads(r.stdout);(E/'NBN_CACHE_END.json').write_text(json.dumps(x['cache'],indent=2)+'\n');(E/'NBN_RESOLVED_LIBRARY_PIN.json').write_text(json.dumps(x['resolved_aeneas'],indent=2)+'\n')
start=json.loads((E/'NBN_CACHE_START.json').read_text());changed={k:dict(before=v,after=x['cache'].get(k)) for k,v in start.items() if x['cache'].get(k)!=v};assert not changed,changed
(E/'NBN_HOST_AUDIT.json').write_text(json.dumps(dict(cache_start_files=len(start),cache_end_files=len(x['cache']),existing_objects_unchanged=True,resolved_aeneas_count=len(x['resolved_aeneas']),live_own_provers=x['live_own_provers'],persistent_cache_retained=cache),indent=2)+'\n')
# Own scratch cleanup only. Never remove persistent cache, source scratch or receipts.
# Submit once; on transport ambiguity recover the receipt read-only.
cleanup=f'''from pathlib import Path
import shutil,json
b=Path({B!r});result={{'persistent_cache_retained':{cache!r},'removed':{{}},'sources_and_receipts_retained':True}}
for name in ['NBN_target','NBN_tmp']:
 p=b/name;assert p.parent==b and not p.is_symlink()
 result['removed'][str(p)]=sum(f.stat().st_size for f in p.rglob('*') if f.is_file()) if p.exists() else 0
 if p.exists():shutil.rmtree(p)
(b/'NBN_HOST_CLEANUP.json').write_text(json.dumps(result,indent=2)+'\\n');print(json.dumps(result))
'''
r=subprocess.run(['ssh','-o','ConnectTimeout=15',H,'python3','-'],input=cleanup,capture_output=True,text=True)
if r.returncode==255:
 r=subprocess.run(['ssh','-o','ConnectTimeout=15',H,'cat',B+'/NBN_HOST_CLEANUP.json'],capture_output=True,text=True)
assert r.returncode==0,r.stderr
(E/'NBN_HOST_CLEANUP.json').write_text(json.dumps(json.loads(r.stdout),indent=2)+'\n');print('Host pins and cleanup recorded; persistent cache retained.')
