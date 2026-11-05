from pathlib import Path
import json,hashlib,lzma,re,subprocess
E=Path(__file__).resolve().parent
J=lambda p:json.loads(p.read_text())

def qualify(a,expected,needle=None):
 r=J(E/a/'receipt.json');log=(E/a/'stdout.log').read_text()
 assert r['exit_status']==expected,(a,'exit')
 assert ('VERIFICATION:- SUCCESSFUL'if expected==0 else'VERIFICATION:- FAILED')in log,(a,'verdict')
 assert not any(x in log.lower()for x in ['timed out','unwinding failures','out of memory','could not compile']),a
 if expected:
  failures=[l for l in log.splitlines()if l.startswith('Failed Checks:')]
  if r['module'].endswith(('KMX_checks::KMX_ptr_wrong','KMX_checks::KMX_slice_wrong')):
   assert len(failures)==1 and failures[0]=="Failed Checks: This is a placeholder message; Kani doesn't support message formatted at runtime",(a,failures)
   assert 'in core::panicking::assert_failed_inner'in log,(a,'not assert_eq panic')
  else:assert failures and all('assertion failed:'in l for l in failures),(a,failures)
  if needle:assert all(needle in l for l in failures),(a,failures)
 assert J(E/(a+'-graph-check.json'))['graph_matches_frozen']
 lock=J(E/(a+'-lock-check.json'));assert lock['unchanged']and lock['before']==lock['after']=='5782e6a32026fdd95d252d0db7ea20b16716e6deb4f5a397e744886bb6ba22ef'
 assert not J(E/(a+'-source-check.json'))['errors']
 assert r['env']['CARGO_NET_OFFLINE']=='true'and'-Copt-level=3'in r['env']['RUSTFLAGS']
 ad=J(E/(a+'-admission.json'));assert ad['exit']==0 and ad['reservation']['allowed']is True
 return r,log

windows=J(E/'NIG_FILLED_WINDOWS.json')
assert len(windows)==24
expected={(b,k)for b in range(0,64,4)for k in [0,32]if b+3>=k}
assert {(r['prefix_base'],r['window_base'])for r in windows}==expected
coverage=set()
for w in windows:
 b,k=w['prefix_base'],w['window_base']
 pos,_=qualify(w['positive'],0);neg,log=qualify(w['control'],1,'words(out[k])[limb] == 0')
 assert pos['module']==neg['module']=='NIG_filled::prefix_frame'
 key='NIG_src/crates/aspis-core/src/NIG_filled.rs'
 assert pos['source_hashes'][key]==neg['source_hashes'][key]
 index=J(E/w['positive']/'SOURCE_INDEX.json');body=lzma.decompress((E/index[key]['payload']).read_bytes()).decode()
 assert all('step::<'+str(p)+'>'in body for p in range(b,b+4))
 assert 'core::ptr::write_bytes(ptr,0,p)'in body and 'ptr.add(p).write(q(kani::any()))'in body
 assert 'out.set_len(p)'in body and 'out.resize(p+1,Q::ZERO)'in body
 assert 'out.as_ptr()==ptr&&out.len()==p+1&&out.capacity()==cap'in body
 assert f'let k:usize={k}+'in body
 assert all('step::<'+str(p)+'>'in log for p in range(b,b+4)),(b,k,'control missing specialization')
 coverage.update((p,j)for p in range(b,b+4)for j in range(k,k+32)if j<=p)
assert coverage=={(p,j)for p in range(64)for j in range(p+1)}
for a in ['NIG_K092','NIG_K093']:qualify(a,1)
qualify('NIG_K094',0);qualify('NIG_K095',1,'words(out)[limb] == words(source)[limb]')
patch=E.parent/'kani-mitig-20261028/KMX_copy_stubs.patch'
assert hashlib.sha256(patch.read_bytes()).hexdigest()=='bcdf749b78eb6143789500d98d64ec3d407b8a17a6d1290c70c822473e8e9a67'
frozen=subprocess.check_output(['git','show','4bb3b3f:crates/aspis-core/src/r0/heap.rs'],text=True)
assert 'out.try_reserve_exact(n).map_err(|_| Error::Allocation)?;'in frozen and'out.resize(n, value);'in frozen
assert not re.search(r'\bstatic\s+(mut\s+)?\w+\s*:',(E/'NIG_filled.patch').read_text())
assert 'Option<fn'not in(E/'NIG_filled.patch').read_text()
pairs=[]
for start,names in [(9,['common_lhs','common_rhs','common_count','common_frame']),(19,['low_lhs','low_rhs','low_order','low_scalar','low_scale','low_frame']),(31,['final_power','final_part','final_sum','final_product','final_order','final_result'])]:
 for i,name in enumerate(names):
  a,b=f'NIG_K{start+2*i:03}',f'NIG_K{start+2*i+1:03}'
  p,_=qualify(a,0);c,_=qualify(b,1)
  assert p['module']==c['module']=='weights::NIG_stages::'+name
  key='NIG_src/crates/aspis-r1-cost-probe/src/NIG_stages.rs';assert p['source_hashes'][key]==c['source_hashes'][key]
  pairs.append(dict(family=name,positive=a,control=b))
for a in ['NIG_K017','NIG_K018']:qualify(a,1)
out=dict(status='PASS',filled_windows=windows,covered_prefix_cell_pairs=len(coverage),filled_native_domain='n64 QM31 ZERO, SAME successful reserve, initialized zero prefix, arbitrary next cell and remaining spare uninitialized; allocator Err/abort retained',clone_pair=['NIG_K094','NIG_K095'],kmx_core_negative_controls=['NIG_K092','NIG_K093'],kmx_probe_negative_controls=['NIG_K017','NIG_K018'],kmx_patch_sha256=hashlib.sha256(patch.read_bytes()).hexdigest(),independent_pairs=pairs,no_native_field_products=True,no_writable_static=True,no_function_pointer=True,excluded=['NIG_K001 compile error','NIG_K002/K003/K004/K005/K008/K043 timeout'],support_only=['NIG_K006/K007 fixed63 zeroed backing'],qualified_rows=['TX2:045'],source_association='NIG_SOURCE_ASSOCIATION.md')
(E/'NIG_NATIVE_VALIDATION.json').write_text(json.dumps(out,indent=2)+'\n')
print('PASS filled24 window pairs,2080 covered positions, clone/control and KMX;16 independent observation pairs')
