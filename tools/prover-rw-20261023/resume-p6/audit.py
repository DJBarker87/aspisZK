"""Focused packet consistency audit, not a proof replay or native erasure theorem."""
from pathlib import Path
import hashlib,json,subprocess,sys
D=Path(__file__).resolve().parent;ROOT=D.parents[2]
E=ROOT/'docs/research/100bit-spend-path-20261013/evidence/prover-rw-20261023/resume-p6'
sha=lambda b:hashlib.sha256(b).hexdigest()
assert subprocess.check_output(['git','branch','--show-current'],cwd=ROOT,text=True).strip()=='codex/cx-prover-rw-20261023'
assert not subprocess.check_output(['git','diff','1097f5bef9','--','crates','programs'],cwd=ROOT)
revisions=[];rows=[]
for tag,local,attempt in [('original',D,58),('compact',D/'compact',59)]:
 m=json.loads((local/'source-map.json').read_text())
 z=(local/'zeroize-instrumented.rs.txt').read_text()
 for patch in reversed(m['zeroize']['patches']):
  assert z.count(patch['after'])==1
  z=z.replace(patch['after'],patch['before'])
 assert z==(local/'zeroize-original.rs.txt').read_text()
 assert sha(z.encode())==m['zeroize']['original_sha256']
 g=(local/'getrandom-error-instrumented.rs.txt').read_text()
 g=g.replace(m['getrandom']['after'],m['getrandom']['before'])
 assert g==(local/'getrandom-error-original.rs.txt').read_text()
 assert sha((local/'proof/selected.rs').read_bytes())==m['selected_sha256']
 assert (local/'proof/selected.rs').read_bytes()==(D.parent/'factory-state/preflight/lib.rs').read_bytes().replace(b'ProverRwFactoryState',b'ProverRwResumeP6')
 assert m['semantic_erasure_proved'] is False
 P=E/'packet'/f'kani{attempt:03d}'
 receipt=json.loads((P/'receipt.json').read_text())
 pre=json.loads((P/'preflight.json').read_text())
 before=json.loads((P/'admission-before.json').read_text())
 assert before['allowed'] and before['reserve_check']
 assert before['projected_reserved_bytes']<55*2**30
 assert before['requested_bytes']==4*2**30
 go=json.loads((P/'admission-barrier.json').read_text())
 assert go['allowed'] and go['reserve_check'] and go['requested_bytes']==0
 assert go['projected_reserved_bytes']<55*2**30
 assert go['limits']=={'memory.high':str(3*2**30),'memory.max':str(4*2**30),'memory.swap.max':'0','pids.max':'64'}
 h=json.loads((P/'go-hashes.json').read_text())['source_sha256']
 assert h==pre['source_sha256']==receipt['source_sha256']
 for suffix,relative in [('vendor/zeroize-1.8.1/src/lib.rs','zeroize-instrumented.rs.txt'),('vendor/getrandom-0.3.4/src/error.rs','getrandom-error-instrumented.rs.txt'),('proof/selected.rs','proof/selected.rs'),('proof/lib.rs','proof/lib.rs')]:
  matches=[v for p,v in h.items() if p.endswith('/'+suffix)]
  assert len(matches)==1 and matches[0]==sha((local/relative).read_bytes()),suffix
 post=json.loads((P/'postrun.json').read_text());assert post['unchanged'] and post['source_sha256']==h
 assert receipt['pins_unchanged'] and receipt['actual_invocations']==1
 res=json.loads((P/'resources.json').read_text());assert res['peak_swap_bytes']==0
 assert receipt['semantic_erasure_proved'] is False and receipt['native_world_refinement_proved'] is False
 # Metadata/package/compiler/sysroot pins must all be present before and at go.
 for needle in ['vendor/zeroize-1.8.1/src/lib.rs','vendor/getrandom-0.3.4/src/error.rs','proof/selected.rs','.kani/kani-0.67.0/toolchain/bin/rustc','.kani/kani-0.67.0/toolchain/lib/rustlib/x86_64-unknown-linux-gnu/lib/']:
  assert any(needle in p for p in h),needle
 rows.append(dict(attempt=attempt,source_revision=receipt['source_revision'],source_map_sha256=sha((local/'source-map.json').read_bytes()),command=receipt['command'],exit_status=receipt['exit_status'],wall_seconds=receipt['wall_seconds'],target_gnu_peak_rss_kib=receipt['peak_rss_kib'],sampled_aggregate_rss_kib=res['sampled_peak_aggregate_rss_kib'],cgroup_peak_bytes=res['cgroup_memory_peak_bytes'],swap_bytes=res['peak_swap_bytes'],dependency_fingerprint=receipt['dependency_fingerprint'],print_axioms=receipt['print_axioms']))
for p in E.rglob('*.json'):
 assert p.stat().st_size<=5_000_000,(str(p),'store hash/size only')
assert rows[0]['exit_status']==124
assert rows[0]['source_map_sha256']!=rows[1]['source_map_sha256']
assert (D/'reservation.py').read_bytes()==(D.parent/'factory-state/reservation.py').read_bytes()
assert (D/'reservation_base.py').read_bytes()==(D.parent/'factory-state/reservation_base.py').read_bytes()
ledger=dict(schema='ProverRwResumeP6-budget-v1',entry=dict(Kani=57,Lean=236,extraction=54,backend=15),exit=dict(Kani=59,Lean=236,extraction=54,backend=15),ceilings=dict(Kani=60,Lean=260,extraction=56,backend=16),actual_invocations=dict(Kani=2,Lean=0,Charon=0,Aeneas=0),this_step_Kani_limit=2,last_Kani_reserved=True,Rust_checks_tests=0,ELF_commands=0,prepared_paired_check='unexecuted/unvalidated',full_manifest=0)
out=dict(schema='ProverRwResumeP6-focused-integrity-v1',command=sys.argv,source_revision=subprocess.check_output(['git','rev-parse','HEAD'],cwd=ROOT,text=True).strip(),runs=rows,budgets=ledger,source_contract_proved=False,semantic_erasure_proved=False,native_world_transport_proved=False,print_axioms='N/A: no Lean declarations',claim='source/receipt consistency only; no privacy or adoption closure')
Path(sys.argv[1]).write_text(json.dumps(out,indent=2)+'\n')
print('PASS focused source and receipt consistency; native/P6/erasure/E1/finite16 remain open')
