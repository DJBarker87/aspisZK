"""Optimized writer diagnostic, not timing, whole-client privacy, or a new gate replay."""
from pathlib import Path
import hashlib,json,os,resource,subprocess
H=Path('/home/dombarker/project-offloads/codex-pv-uc-20261029');O=H/'final-gates/d561/writer';O.mkdir(exist_ok=False)
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
p=H/'audit-src/Cargo.toml';before=p.read_bytes();name='pv-uc-writer-d561';assert name.encode() not in before
p.write_bytes(before+('\n[[bin]]\nname = "'+name+'"\npath = '+json.dumps(str(H/'writer-d561.rs'))+'\n').encode())
e=dict(os.environ,PATH='/home/dombarker/.cargo/bin:/usr/bin:/bin',CARGO_TARGET_DIR=str(H/'native-target'),RUSTFLAGS='--cfg getrandom_backend="linux_raw" --check-cfg=cfg(getrandom_backend,values("linux_raw")) -C link-arg=-Wl,--threads=4')
c=['taskset','--cpu-list','0-3','cargo','+1.94.1','build','--manifest-path',str(p),'--profile','client','--locked','--offline','-j','4','--features','r1p-check,aspis-r1-cost-probe/ct-host-prover','--bin',name]
print('EXPECTED WORK: incremental optimized diagnostic compilation/link and two constant public-operand executions; no proof generation or timing',flush=True)
subprocess.run(c,env=e,check=True)
b=H/'native-target/client'/name
resource.setrlimit(resource.RLIMIT_CORE,(0,0))
a=subprocess.run([str(b)],capture_output=True);assert a.returncode==0 and a.stdout==b'"public operand"\n' and not a.stderr
with open('/dev/full','wb',buffering=0) as full:r=subprocess.run([str(b)],stdout=full,stderr=subprocess.PIPE)
assert r.returncode==-6 and r.stderr==b'client panic\n',(r.returncode,r.stderr)
x=dict(status='CHECKED WRITER COUNTEREXAMPLE',evidence_class='Finite deployed-configuration diagnostic of the reached serde_json Value Display and println expressions; no whole-client equivalence claim',command=c,source_sha256=sha(H/'writer-d561.rs'),binary_sha256=sha(b),binary_bytes=b.stat().st_size,manifest_before_sha256=hashlib.sha256(before).hexdigest(),manifest_after_sha256=sha(p),string_writer='Ok; exact JSON string',failing_fmt_writer='Err(fmt::Error)',stdout_success=dict(exit=a.returncode,stdout=a.stdout.decode()),stdout_full=dict(exit=r.returncode,stderr=r.stderr.decode()),consequence='The actual println writer is fallible stdout, not String. Pure serialization of a public Value may be abstracted separately, but the stdout prefix/error/abort event must still be bound; the new String exemption alone does not discharge this call.')
(O/'native.json').write_text(json.dumps(x,indent=2)+'\n');print(json.dumps(x),flush=True)
