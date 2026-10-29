"""Native additive/control review: exact cfg erasure and frozen graph every run."""
from pathlib import Path
import hashlib,json,re,subprocess,sys
sys.dont_write_bytecode=True
E=Path(__file__).resolve().parent;R=E.parent.parent;sha=lambda b:hashlib.sha256(b).hexdigest();obj=lambda p:json.loads(p.read_text())
sys.path.insert(0,str(E));from NEB_patch_value import replay
F='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387';frozen=lambda p:subprocess.check_output(['git','show',F+':'+p],cwd=R)
files=replay((E/'NEB_additive.patch').read_text(),R)
for path,ns in [('crates/aspis-core/src/field.rs',['NEB_additive','NEB_reducer']),('crates/aspis-core/src/field/wide_exact.rs',['NEB_wide'])]:
 text=files[path].decode();count=0;kept=[]
 for line in text.splitlines(keepends=True):
  if '#[cfg_attr(kani,kani::' in line and any(n+'::' in line for n in ns):count+=1
  elif line.startswith('#[cfg(kani)] #[path=') and any('mod '+n+';' in line for n in ns):pass
  else:kept.append(line)
 assert count==(18 if len(ns)==2 else 7),(path,count)
 erased=''.join(kept).removesuffix('\n');assert erased.encode()==frozen(path),'cfg erasure differs '+path
lib='crates/aspis-core/src/lib.rs';assert files[lib].replace(b'#![cfg_attr(kani,feature(allocator_api))]\n',b'')==frozen(lib)
lock=sha(frozen('Cargo.lock'));kmx=sha((E.parent/'kani-mitig-20261028/KMX_copy_stubs.patch').read_bytes());results=[];graph=set()
jobs=[dict(attempt=f'NEB_K{n:03}',expected_exit=e,target='field::NEB_additive::KMX_checks::KMX_ptr_'+('correct' if e==0 else 'wrong')) for n,e in [(9,0),(10,1)]]
jobs+=obj(E/'NEB_ADDITIVE_RUNS.json')[:4]+obj(E/'NEB_ADDITIVE_REPAIRED_RUNS.json')+obj(E/'NEB_FINAL_RUNS.json')
for job in jobs:
 a=job['attempt'];rc=obj(E/a/'receipt.json');g=obj(E/(a+'-graph-check.json'));lc=obj(E/(a+'-lock-check.json'));log=(E/a/'stdout.log').read_text();status=job['expected_exit']
 assert rc['exit_status']==status and rc['target']==job['target'],a
 assert rc['env']['CARGO_NET_OFFLINE']=='true' and rc['env']['CARGO_PROFILE_DEV_OPT_LEVEL']=='3'
 assert rc['swaps']=='0' and rc['limits']=={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'}
 assert lc==dict(before=lock,after=lock,unchanged=True)
 assert g['graph_matches_frozen'] and g['exact_frozen_selected_graph'] and not g['edge_errors'] and not g['new_package_tuples']
 assert len(g['resolved_features_all_crates'])==g['resolved_packages']==441
 assert next(r['features'] for r in g['selected_closure'] if r['name']=='aspis-core')==['r0'];graph.add(g['canonical_graph_sha256'])
 assert not obj(E/(a+'-source-check.json'))['errors']
 for p,raw in files.items():
  if int(a[-3:])<=15 and p.endswith('NEB_additive.rs'):raw=raw.replace(b'impl kani::Arbitrary for M31 {fn any()->Self{M31(kani::any::<u32>())}}\n',b'')
  assert rc['source_hashes']['NEB_src/'+p]==sha(raw),(a,p)
 assert rc['copy_patch_sha256']==kmx and obj(E/(a+'-tool-check.json'))==obj(E/'NEB_TOOL_PINS.json')
 assert '--locked' not in rc['native_command'] and 'VERIFICATION:- '+('SUCCESSFUL' if status==0 else 'FAILED') in log
 assert re.findall(r'\*\* (\d+) of \d+ failed',log)[-1]==str(status)
 if job.get('failure'):assert job['failure'] in log.split('Failed Checks:',1)[1]
 assert not re.search(r'error:|timed out|VERIFICATION:- UNKNOWN',log)
 results.append(dict(attempt=a,target=rc['target'],receipt_sha256=sha((E/a/'receipt.json').read_bytes()),exit_status=status,wall_seconds=rc['wall_seconds'],peak_rss_kib=rc['peak_rss_kib'],swaps=rc['swaps']))
assert len(graph)==1
out=dict(schema='NEB-additive-native-review-v1',frozen_revision=F,native_results=results,patch_sha256=sha((E/'NEB_additive.patch').read_bytes()),reference_sha256=sha((E/'NEB_additive_reference.rs').read_bytes()),cfg_erasure='Entire field.rs, wide_exact.rs and lib.rs byte-identical after removing only cfg(kani) instrumentation',copy_patch_sha256=kmx,copy_controls=['NEB_K009','NEB_K010'],array_shape_controls=['NEB_K032','NEB_K033','NEB_K034','NEB_K035','NEB_K036'],pure_record_shape='M31 scalar newtype and CM31/QM31/WideExact fixed records; ruling t pure record exception; all production verified stubs are scalar M31 methods',rule14_dependent=False,trust='NativeContractSemanticTransport: P6/D188 reclassification, never removal',remaining='Exact extracted safe reference/cohort/PacketDomain/state/effect association and inner physical interpretation discharge; no composition inferred by native result alone')
if '--check' in sys.argv:assert obj(E/'NEB_ADDITIVE_REVIEW.json')==out
else:(E/'NEB_ADDITIVE_REVIEW.json').write_text(json.dumps(out,indent=1)+'\n')
print(json.dumps(dict(native_review_passed=True,attempts=len(results),composed_credit_before_Lean=0)))
