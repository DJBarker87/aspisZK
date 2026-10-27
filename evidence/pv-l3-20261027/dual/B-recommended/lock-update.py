from pathlib import Path
import subprocess,json,time,tomllib,hashlib,difflib,sys
H=Path('/home/dombarker/project-offloads/codex-pv-l3-20261026');R=H/'dual-B-recommended';O=H/'recommended-lock';O.mkdir(exist_ok=False)
p=R/'tools/r1-cost-probe/Cargo.lock';old=p.read_bytes();cg=Path('/sys/fs/cgroup'+Path('/proc/self/cgroup').read_text().split('0::')[1].strip())
cmd=['/home/dombarker/.cargo/bin/cargo','update','--offline','--workspace','--manifest-path','tools/r1-cost-probe/Cargo.toml'];t=time.monotonic()
with (O/'stdout.log').open('w') as so,(O/'stderr.log').open('w') as se:r=subprocess.run(['/usr/bin/time','-v','-o',str(O/'time.log'),*cmd],cwd=R,stdout=so,stderr=se)
new=p.read_bytes();a=tomllib.loads(old.decode())['package'];b=tomllib.loads(new.decode())['package']
registry=lambda xs:{(v['name'],v['version'],v['source']):v for v in xs if 'source' in v}
paths=lambda xs:{v['name']:v for v in xs if 'source' not in v}
pa,pb=paths(a),paths(b);diff=''.join(difflib.unified_diff(old.decode().splitlines(True),new.decode().splitlines(True),fromfile='a/tools/r1-cost-probe/Cargo.lock',tofile='b/tools/r1-cost-probe/Cargo.lock'));(O/'lockfile.diff').write_text(diff)
rec=dict(target=cmd,source_revision='237e13556180d2ce0320a2760f89b35b5f4f02bb',exit_status=r.returncode,wall_seconds=time.monotonic()-t,registry_entries_unchanged=registry(a)==registry(b),registry_entries_before=len(registry(a)),registry_entries_after=len(registry(b)),path_changes={k:{'before':pa.get(k),'after':pb.get(k)} for k in sorted(set(pa)|set(pb)) if pa.get(k)!=pb.get(k)},old_sha256=hashlib.sha256(old).hexdigest(),new_sha256=hashlib.sha256(new).hexdigest(),limits={n:(cg/n).read_text().strip() for n in ['memory.high','memory.max','memory.swap.max','pids.max']},cgroup_memory_peak_bytes=int((cg/'memory.peak').read_text()),cgroup_swap_peak_bytes=int((cg/'memory.swap.peak').read_text()),print_axioms='N/A (no Lean)',diff=diff)
(O/'receipt.json').write_text(json.dumps(rec,indent=2)+'\n');print(json.dumps(rec));sys.exit(0 if r.returncode==0 and rec['registry_entries_unchanged'] else 90)
