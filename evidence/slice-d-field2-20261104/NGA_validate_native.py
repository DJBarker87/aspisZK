"""Read-only validation of inherited native support; never runs a prover."""
from pathlib import Path
import importlib.util,sys,json,hashlib
sys.dont_write_bytecode=True
E=Path(__file__).resolve().parent;T=E.parent/'slice-d-field-20261104'
p=T/'NFT_certify.py';s=importlib.util.spec_from_file_location('NGA_readonly_NFT',p);m=importlib.util.module_from_spec(s);s.loader.exec_module(m)
rows=[]
for a,b in [(24,25),(26,27),(28,29),(78,79),(80,81),(82,83),(84,85),(86,87),(88,89),(98,99)]:
 x,y=m.pair(a,b)
 rows.append(dict(positive=x['attempt'],control=y['attempt'],positive_receipt_sha256=m.sha((T/x['attempt']/'receipt.json').read_bytes()),control_receipt_sha256=m.sha((T/y['attempt']/'receipt.json').read_bytes()),status='VALID_SUPPORT_ONLY'))
for a,b in [(30,31),(32,33)]:
 x,y=m.copy_pair(a,b);rows.append(dict(positive=x['attempt'],control=y['attempt'],status='VALID_COPY_SUPPORT_ONLY'))
x,_=m.native(100,1);assert '--cfg NFT_bad_argument' in x['env']['RUSTFLAGS']
rows.append(dict(control='NFT_K100',status='VALID_ARGUMENT_CONTROL_ONLY'))
expected=json.loads((E/'NGA_NATIVE_PINS.json').read_text())
for name,pin in expected.items():assert m.sha((E.parents[1]/name).read_bytes())==pin['sha256']
patch=E.parents[1]/'evidence/kani-mitig-20261028/KMX_copy_stubs.patch'
assert m.sha(patch.read_bytes())=='bcdf749b78eb6143789500d98d64ec3d407b8a17a6d1290c70c822473e8e9a67'
result=dict(status='PASS',mode='read-only inherited certificate validation; no Kani rerun',checks=rows,NFT_validator_sha256=m.sha(p.read_bytes()),KMX_patch_sha256=m.sha(patch.read_bytes()),closure_credit=False)
(E/'NGA_NATIVE_REVALIDATION.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({'status':result['status'],'support_groups':len(rows),'closure_credit':False}))

# The new data-step family is independent of inherited chronology support.
new=[]
for i in range(1,9):
 a=f'NGA_K{i:03}';r=json.loads((E/a/'receipt.json').read_text());g=json.loads((E/(a+'-graph-check.json')).read_text());lock=json.loads((E/(a+'-lock-check.json')).read_text());ad=json.loads((E/(a+'-admission.json')).read_text())
 assert ad['exit']==0 and ad['reservation']['allowed']is True
 assert r['limits']=={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'}and int(r['swaps'])==0
 assert g['graph_matches_frozen']and lock['unchanged']and lock['before']==lock['after']=='5782e6a32026fdd95d252d0db7ea20b16716e6deb4f5a397e744886bb6ba22ef'
 assert r['env']['CARGO_NET_OFFLINE']=='true'and r['env']['CARGO_PROFILE_DEV_OPT_LEVEL']=='3'
 assert next(p['features']for p in g['selected_closure']if p['name']=='aspis-core')==['r0']
 expected=0 if i in [1,3,5,7]else 1;assert r['exit_status']==expected
 output=(E/a/'stdout.log').read_text();assert 'VERIFICATION:- '+('FAILED'if expected else 'SUCCESSFUL')in output
 assert 'CBMC timed out'not in output
 if expected:assert '** 1 of 'in output
 for name,h in r['source_hashes'].items():assert hashlib.sha256((E/a/'sources'/name).read_bytes()).hexdigest()==h
 src=(E/a/'sources/NGA_src/crates/aspis-core/src/NGA_outer.rs').read_text()
 assert 'static mut'not in src and 'Option<'not in src and '#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]'in src
 new.append({k:r[k]for k in ['attempt','module','exit_status','wall_seconds','peak_rss_kib','swaps']})
for a,b in [(1,2),(3,4),(5,6),(7,8)]:
 x=json.loads((E/f'NGA_K{a:03}/receipt.json').read_text());y=json.loads((E/f'NGA_K{b:03}/receipt.json').read_text());assert x['source_hashes']==y['source_hashes']
 if a==1:assert x['env']==y['env']
 else:assert y['env']['RUSTFLAGS']==x['env']['RUSTFLAGS']+' --cfg NGA_invert'
(E/'NGA_NATIVE_NEW_RESULTS.json').write_text(json.dumps(dict(status='PASS_SUPPORT_ONLY',checks=new,KMX_sha256=m.sha(patch.read_bytes()),whole_buffer_function_runs=False,field_multiplication_in_Kani=False,closure_credit=False),indent=2)+'\n')
print(json.dumps(dict(new_native_checks=len(new),closure_credit=False)))
