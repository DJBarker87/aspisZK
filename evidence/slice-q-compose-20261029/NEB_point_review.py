"""Revalidate committed peer point/line packets; no status credit by citation."""
from pathlib import Path
import json,hashlib,subprocess,re,sys
sys.dont_write_bytecode=True
E=Path(__file__).resolve().parent;R=E.parent.parent;I=E/'NEB_IMPORTED_POINT';sha=lambda b:hashlib.sha256(b).hexdigest()
sys.path[:0]=[str(E.parent/'native-ledger3-20261029'),str(E.parent/'native-ledger2-20261028')]
import NDT_review
from NEB_patch_value import replay
M=json.loads((E/'NEB_POINT_IMPORTS.json').read_text())
for f in M['files']:
 b=(R/f['path']).read_bytes();assert sha(b)==f['sha256'];assert b==subprocess.check_output(['git','show',M['revision']+':'+f['source_path']],cwd=R)
lock=sha(subprocess.check_output(['git','show','4bb3b3f51e16b4525f1d10336e2b0bcbbd775387:Cargo.lock'],cwd=R));kmx=sha((E.parent/'kani-mitig-20261028/KMX_copy_stubs.patch').read_bytes())
checks=[]
for n,expected in [(17,0),(18,1),(12,0),(13,1),(29,0),(30,1),(31,0),(32,1)]:
 a=f'NEA_K{n:03}';d=json.loads((I/a/'receipt.json').read_text());log=(I/a/'stdout.log').read_text();g=json.loads((I/(a+'-graph-check.json')).read_text());l=json.loads((I/(a+'-lock-check.json')).read_text())
 assert d['exit_status']==expected and d['swaps']=='0'
 assert d['limits']=={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'}
 assert d['env']['CARGO_NET_OFFLINE']=='true' and d['env']['CARGO_PROFILE_DEV_OPT_LEVEL']=='3'
 assert d['copy_patch_sha256']==kmx and l['before']==l['after']==lock and l['unchanged']
 assert g['graph_matches_frozen'] and not g['edge_errors'] and not g['new_package_tuples'] and g['lock_sha256']==lock
 NDT_review.check_features(g,'library-helper')
 assert not json.loads((I/(a+'-source-check.json')).read_text())['errors']
 assert 'VERIFICATION:- '+('SUCCESSFUL' if expected==0 else 'FAILED') in log
 assert re.findall(r'\*\* (\d+) of \d+ failed',log)[-1]==str(expected)
 if n in [18,30]:assert ('point_post' if n==18 else 'line_post') in log.split('Failed Checks:')[1]
 patched=replay((I/a/'NEA_harness.patch').read_text(),R)
 for f,h in d['source_hashes'].items():
  if f.startswith('NEA_src/') and f[8:] in patched:assert sha(patched[f[8:]])==h,(a,f)
  elif f=='NEA_src/Cargo.lock':assert h==lock
 # Gate/source pin JSON are attested by each invocation's graph/source checks; native Rust bytes are independently reconstructed above.
 checks.append(dict(attempt=a,receipt_sha256=sha((I/a/'receipt.json').read_bytes()),exit_status=expected,wall_seconds=d['wall_seconds'],peak_rss_kib=d['peak_rss_kib'],swaps=d['swaps']))
lean=[]
for n in [6,15,50,51,59,60]:
 a=f'NEA_L{n:03}';d=json.loads((I/a/'receipt.json').read_text());assert d['exit_status']==0
 for f,h in d['source_hashes'].items():assert sha((I/f.removeprefix('NEA_generated/')).read_bytes())==h
 assert d['print_axioms'] and all('sorryAx' not in x and all(y.strip() in ['propext','Classical.choice','Quot.sound'] for y in re.search(r'depends on axioms: \[(.*?)\]',x)[1].split(',')) for x in d['print_axioms'])
 lean.append(dict(attempt=a,receipt_sha256=sha((I/a/'receipt.json').read_bytes()),print_axioms=d['print_axioms']))
# This review does not use K009/016/019/022/028 (failed or timed out).
out=dict(revision=M['revision'],verified_files=len(M['files']),native=checks,lean=lean,trust='NativeContractSemanticTransport option A: P6/D188 reclassification; canonical opaque product reply selected by emitted Lean law',physical_interpretation='NEA_PointComplete.emitted_interpretation discharges the non-root lower record law; caller index domain still required',composed_credit=0,copy_patch_sha256=kmx)
(E/'NEB_POINT_REVIEW.json').write_text(json.dumps(out,indent=1)+'\n');print(json.dumps(dict(verified_files=len(M['files']),native=len(checks),lean=len(lean),composed_credit=0)))
