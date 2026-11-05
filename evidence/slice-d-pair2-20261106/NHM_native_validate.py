"""Additive source-cut, frozen-graph and semantic-control qualification."""
from pathlib import Path
import hashlib,json,lzma,re,subprocess
E=Path(__file__).resolve().parent
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
J=lambda n:json.loads((E/n).read_text())
LIMITS={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'}
def source(a,n):
 idx=J(a+'/SOURCE_INDEX.json');row=idx[n];raw=lzma.decompress((E/row['payload']).read_bytes())
 assert len(raw)==row['bytes']and hashlib.sha256(raw).hexdigest()==row['sha256']==J(a+'/receipt.json')['source_hashes'][n]
 return raw.decode()
def body(s,name):
 start=s.index('fn '+name+'(');start=s.index('{',start);end=start+1;depth=1
 while depth:depth+=(s[end]=='{')-(s[end]=='}');end+=1
 return s[start+1:end-1]
def inner(s,marker):
 start=s.index(marker);start=s.index('{',start);end=start+1;depth=1
 while depth:depth+=(s[end]=='{')-(s[end]=='}');end+=1
 return s[start+1:end-1]
norm=lambda s:re.sub(r'\s+','',s)
frozen=subprocess.check_output(['git','show','4bb3b3f:crates/aspis-r1-cost-probe/src/weights.rs'],text=True)
PAIRS=[('filled',g,4 if g==0 else 6+2*(g-1),'NHM_filled::filled'+f'{g:02}')for g in range(6)]
PAIRS += [('partial',g,17+2*g,'weights::NHM_windows::partial'+f'{g:02}')for g in range(8)]
PAIRS += [('high',g,33+2*g,'weights::NHM_windows::high'+f'{g:02}')for g in range(6)]
PAIRS += [('byte64',g,61+2*g,'weights::NHM_windows::byte'+f'{g:02}')for g in range(8)]
# Further families are admitted only after both complete semantic verdicts exist.
PAIRS += [('init',g,(77 if g==0 else 78+2*g),'NHM_init::init'+f'{g:02}')for g in range(4)]
rows=[];pending=[]
for family,g,number,harness in PAIRS:
 names=[f'NHM_K{number:03}',f'NHM_K{number+1:03}']
 if not all((E/a/'receipt.json').exists()for a in names):pending.append([family,g]);continue
 rs=[J(a+'/receipt.json')for a in names]
 for k,(a,r)in enumerate(zip(names,rs)):
  assert r['module']==harness and r['exit_status']==k,(a,'verdict')
  text=(E/a/'stdout.log').read_text()
  assert ('VERIFICATION:- FAILED'if k else'VERIFICATION:- SUCCESSFUL')in text
  assert 'unwinding failures'not in text and 'timed out'not in text.lower()
  if k:assert 'assertion failed'in text,(a,'semantic control required')
  assert r['limits']==LIMITS and str(r['swaps'])=='0'
  ad=J(a+'-admission.json');assert ad['exit']==0 and ad['reservation']['allowed']is True
  graph=J(a+'-graph-check.json');lock=J(a+'-lock-check.json');pins=J(a+'-source-check.json')
  assert not pins['errors']and graph['graph_matches_frozen']and not graph['new_package_tuples']and not graph['edge_errors']
  assert lock['unchanged']and lock['before']==lock['after']=='5782e6a32026fdd95d252d0db7ea20b16716e6deb4f5a397e744886bb6ba22ef'
  assert r['env']['CARGO_NET_OFFLINE']=='true'and '-Copt-level=3'in r['env']['RUSTFLAGS']
  assert '--locked'not in r['native_command']and '--no-default-features'not in r['native_command']
  assert r['native_command'][r['native_command'].index('--harness-timeout')+1]=='90s'
  rootname=r.get('root_package','aspis-r1-cost-probe');root=next(p for p in graph['selected_closure']if p['name']==rootname)
  if rootname=='aspis-r1-cost-probe':
   assert {'default','private-leaf-salts','optimized-terminal','program-build'}<=set(root['features'])
   statement=next(p for p in graph['selected_closure']if p['name']=='aspis-statement')
   assert {'r0','pool-v1-kernel'}<=set(statement['features'])
  else:assert rootname=='aspis-core'and 'r0'in root['features']
 assert rs[0]['source_hashes']==rs[1]['source_hashes'],names
 path='NHM_src/crates/aspis-core/src/NHM_'+('init'if family=='init'else'filled')+'.rs'if family in['filled','init']else'NHM_src/crates/aspis-r1-cost-probe/src/NHM_windows.rs'
 code=source(names[0],path)
 assert not re.search(r'\bstatic\b|Option\s*<\s*fn\b|stub_verified|proof_for_contract',code)
 assert 'KMX_copy_nonoverlapping'in code and 'KMX_copy_from_slice'in code
 if family in ['partial','high','byte64']:
  name={'partial':'partial_dot','high':'high_dot','byte64':'push_byte_products'}[family]
  cut=body(code,{'partial':'partial_window','high':'high_window','byte64':'byte_window'}[family])
  cut=cut.rstrip();assert cut.endswith('Ok(())');cut=cut[:-6]
  if family=='partial':cut=cut.replace('let x=field(f,16*s+j,l);','').replace('push(d,x,common[j],l)','dot.push(field(f,16*s+j),common[j])')
  if family=='byte64':cut=cut.replace('let x=field(f,j,l);','').replace('push(d,x,scratch[j],l)','pair.push(field(f,j),scratch[j])')
  if family=='high':cut=cut.replace('push(d,partials[j],coeffs[j],l)','high.push(partials[s],coeffs[s])')
  expected=inner(body(frozen,name),'for ')
  assert norm(cut)==norm(expected),(family,'source erasure mismatch',cut,expected)
  if family=='byte64':assert 'j<if family==2{4}else if family==1{64}else{16}'in code
 rows.append(dict(family=family,group=g,positive=names[0],negative=names[1],harness=harness,source_erasure=family in['partial','high','byte64'],credit='LOCAL NATIVE OBSERVATION ONLY; composed row needs model, caller domains and audit'))
assert sha(E.parent/'kani-mitig-20261028/KMX_copy_stubs.patch')=='bcdf749b78eb6143789500d98d64ec3d407b8a17a6d1290c70c822473e8e9a67'
out=dict(status='PASS completed pairs; pending explicitly listed',pairs=rows,pending=pending,kmx_patch_sha256=sha(E.parent/'kani-mitig-20261028/KMX_copy_stubs.patch'),field_multiplication_native=False,quarantined=[],suspended=[],excluded=['K001–K003 compile failures','K016 input initialization unwinding','K079 initialization value timeout; replaced actual prefix invariant','K045–K060 byte window restricted to16; superseded on broader domain by K061–K076'])
(E/'NHM_NATIVE_VALIDATION.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(dict(pairs=len(rows),pending=pending)))
