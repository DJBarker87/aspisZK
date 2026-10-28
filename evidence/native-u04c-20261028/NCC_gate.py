"""Own strict graph validator; runs INSIDE the capped unchanged S2W runner."""
from pathlib import Path
import hashlib,json,subprocess,sys,os
B=Path(__file__).resolve().parent;S=B/'NBU_src';a,h=sys.argv[1:]
tools={}
for name,path in [('kani','/home/dombarker/.kani/kani-0.67.0/bin/kani-driver'),('cbmc','/home/dombarker/.kani/kani-0.67.0/bin/cbmc')]:
 p=Path(path);v=subprocess.run([str(p),'--version'],capture_output=True,text=True);assert v.returncode==0,(path,v.stderr)
 tools[name]=dict(path=str(p),version=v.stdout.strip(),sha256=hashlib.sha256(p.read_bytes()).hexdigest())
assert '0.67.0' in tools['kani']['version'] and '6.8.0' in tools['cbmc']['version'],tools
print(json.dumps(dict(tool_pins=tools)),flush=True)
lock=S/'Cargo.lock';before=hashlib.sha256(lock.read_bytes()).hexdigest()
assert before=='5782e6a32026fdd95d252d0db7ea20b16716e6deb4f5a397e744886bb6ba22ef'
assert hashlib.sha256((B/'NBU_KMX_copy_stubs.patch').read_bytes()).hexdigest()=='bcdf749b78eb6143789500d98d64ec3d407b8a17a6d1290c70c822473e8e9a67'
assert (S/'KMX_stubs.rs').read_bytes()==(S/'crates/aspis-statement/src/KMX_stubs.rs').read_bytes()
assert hashlib.sha256((S/'KMX_stubs.rs').read_bytes()).hexdigest()=='ad8efb63d8ff791274c91eff9ccc5b9fb126f5a3ac7f27aa811ca11b8e25c138'
r=subprocess.run(['/home/dombarker/.cargo/bin/cargo','metadata','--manifest-path',str(S/'Cargo.toml'),'--locked','--offline','--format-version','1'],capture_output=True,text=True)
(B/(a+'-metadata.stderr')).write_text(r.stderr);assert r.returncode==0,r.stderr
m=json.loads(r.stdout);k={p['id']:json.dumps([p['name'],p['version'],p.get('source')],separators=(',',':')) for p in m['packages']}
graph={'packages':sorted(k.values()),'edges':sorted([k[n['id']],sorted(k[d] for d in n['dependencies'])] for n in m['resolve']['nodes'])}
expected=(B/'NCC_frozen_graph.sha256').read_text().strip()
actual=hashlib.sha256(json.dumps(graph,sort_keys=True,separators=(',',':')).encode()).hexdigest()
x=dict(graph_matches_frozen=actual==expected,metadata_sha256=hashlib.sha256(r.stdout.encode()).hexdigest(),lock_before_sha256=before,offline=True,KMX_patch_sha256='bcdf749b78eb6143789500d98d64ec3d407b8a17a6d1290c70c822473e8e9a67')
(B/(a+'-graph.json')).write_text(json.dumps(x,indent=2));assert actual==expected,'STOP graph drift'
cmd=['/home/dombarker/.cargo/bin/cargo-kani','kani','--manifest-path',str(S/'crates/aspis-statement/Cargo.toml'),'--lib','-j','1','-Z','unstable-options','-Z','stubbing','-Z','function-contracts','--harness-timeout','90s','--exact','--harness',h,'--output-format','terse']
print(json.dumps(dict(kani_command=cmd)),flush=True)
r=subprocess.run(cmd)
after=hashlib.sha256(lock.read_bytes()).hexdigest();x.update(lock_after_sha256=after,lock_unchanged=after==before,kani_exit=r.returncode)
(B/(a+'-graph.json')).write_text(json.dumps(x,indent=2));assert after==before,'STOP lock drift'
sys.exit(r.returncode)
