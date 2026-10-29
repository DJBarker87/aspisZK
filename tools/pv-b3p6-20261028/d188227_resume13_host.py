"""Deploy-configuration positive matrix gate and matched failing store control."""
from run import H,run
from pathlib import Path
import hashlib,json,subprocess,sys
mode=sys.argv[1];assert mode in ['positive','negative']
p=H/'source/tools/pv-b3p6-20261028/v244-d18813';old=json.loads((H/'features227-resume4.json').read_text())
metadata=['/home/dombarker/.cargo/bin/cargo','+1.94.1','metadata','--offline','--locked','--format-version','1','--manifest-path',str(p/'Cargo.toml')]
x=json.loads(subprocess.check_output(metadata,text=True));pkgs={r['id']:r for r in x['packages']};nodes=[dict(name=pkgs[n['id']]['name'],version=pkgs[n['id']]['version'],source=pkgs[n['id']]['source'],features=n['features'])for n in x['resolve']['nodes']]
assert sorted(nodes,key=lambda n:(n['name'],n['version']))==sorted(old['validation']['nodes'],key=lambda n:(n['name'],n['version']))
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
freeze=json.loads((H/'native227-composition-source-freeze.json').read_text());assert all(sha(H/'source'/name)==s for name,s in freeze.items())
inputs=dict(expected_sha256=sha(H/'d18813-expected.json'),mode=mode,source_revision=(H/'revision').read_text().strip(),rustc=subprocess.check_output(['/home/dombarker/.cargo/bin/rustc','+1.94.1','-vV'],text=True),nodes=nodes,profile=old['profile'],input_hashes={str(f.relative_to(H/'source')):sha(f)for f in p.iterdir()if f.is_file()},instrumentation_record='resume13/d188-fixture-source.json',native_time='optimized compilation then one named source/reference helper comparison; no elimination or proof generation',scope='finite deployed-configuration helper harness; mask-zero modes reproduce the proposed Link counterexample')
(H/('d188-resume13-'+mode+'-inputs.json')).write_text(json.dumps(inputs,indent=2)+'\n')
cmd=['timeout','300','taskset','--cpu-list','0-3','python3',str(H/'d188_gate227_resume13_host.py'),mode]
r=run('d188227-resume13-'+mode,cmd,inputs['native_time'],{'RUSTFLAGS':'-C link-arg=-Wl,--threads=4'})
bin=H/'target/release/d18813'
if bin.is_file():(H/('d188-resume13-'+mode+'-binary.json')).write_text(json.dumps(dict(sha256=sha(bin),bytes=bin.stat().st_size),indent=2)+'\n')
raise SystemExit(r)
