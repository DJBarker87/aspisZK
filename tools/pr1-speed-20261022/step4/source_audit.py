"""Bind final host-only scheduling changes and reused local proof obligations."""
from pathlib import Path
import subprocess,json,hashlib,re,sys
r=Path(__file__).resolve().parents[3];base='96fa2fd74d'
def old(p):return subprocess.check_output(['git','show',base+':'+p],cwd=r,text=True)
def sha(p):return hashlib.sha256((r/p).read_bytes()).hexdigest()
unchanged=['docs/research/v8-r0-zk-20261009/z4/z9c.rs','docs/research/v8-r0-zk-20261009/z4/z9e.rs','docs/research/v8-r0-zk-20261009/c3/check/src/native_workers.rs','docs/research/v8-r0-zk-20261009/c3/check/src/native_m31.rs','crates/aspis-core/src/field.rs','crates/aspis-core/src/field/ct.rs','crates/aspis-r1-cost-probe/src/host_semantic.rs','crates/aspis-r1-cost-probe/src/trace.rs']
for p in unchanged:assert (r/p).read_text()==old(p),p
assert not subprocess.check_output(['git','diff',base,'--name-only','--','programs','crates/aspis-prover','crates/aspis-statement'],cwd=r,text=True).strip()
# Original serial implementations stay verbatim under the disabled-host branch.
for p,first,last in [('crates/aspis-r1-cost-probe/src/host_sumcheck.rs','            for (sample, value)','            let polynomial'),('crates/aspis-r1-cost-probe/src/host_commitment.rs','        for &l in &lanes {','        let mut leaves')]:
 before=old(p);a=before.index(first);b=before.index(last,a);chunk=before[a:b]
 after=(r/p).read_text();assert chunk in after,p
work=(r/'crates/aspis-r1-cost-probe/src/host_work.rs').read_text();assert 'native_workers.rs' in work and 'pool::range(n,k)' in work
result=dict(base=base,unchanged_source_sha256={p:sha(p)for p in unchanged},checks=['original P_R1 gate/checker unchanged','CT scalar kernels and secret recorder unchanged','original semantic oracle and encoder unchanged','original serial scheduling bodies retained verbatim','programs, statement and prover source unchanged','fixed public range helper reuses stage3 partition Kani','sumcheck sample/assignment bijection checked by step4c Kani'],trust='Scoped threads, synchronization, allocator, panic unwind and scheduler remain native assumptions. Trace compares public partitions/completed callbacks, not complete hardware traces or D166 joint transport.')
Path(sys.argv[1]).write_text(json.dumps(result,indent=2)+'\n')
