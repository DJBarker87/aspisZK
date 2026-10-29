"""One permitted Kani run per capped native scope; no extraction scopes."""
from run import H,run
from pathlib import Path
import hashlib,json,subprocess,sys,os
id=int(sys.argv[1]);harness=sys.argv[2];seconds=int(sys.argv[3]) if len(sys.argv)>3 and sys.argv[3].isdigit() else 180
assert 72100<=id<=72199 and seconds in (180,900)
R=H/'resume16';R.mkdir(exist_ok=True)
charged=list(R.glob('K*/receipt/receipt.json'));assert len(charged)<40
label=f'K{id}';retry=0
while (R/label).exists():
 assert not (R/label/'receipt/receipt.json').exists(),'charged ID cannot be reused'
 retry+=1;label=f'K{id}-r{retry}'
P=H/'source/tools/pv-b3p6-20261028';leaf='leaf' in sys.argv
manifest=P/('v244-leaf16' if leaf else 'v244-kani16')/'Cargo.toml'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
prefixes=json.loads((R/'verbatim-prefixes.json').read_text())
for x in prefixes:
 p=H/'source'/x['path'];d=H/'source'/x['prefix_source'];assert sha(d)==x['prefix_sha256'] and sha(p)==x['module_sha256'] and p.read_bytes()[:x['prefix_bytes']]==d.read_bytes()
assert sha(P/'kmx/KMX_stubs.rs')=='ad8efb63d8ff791274c91eff9ccc5b9fb126f5a3ac7f27aa811ca11b8e25c138'
features=['--features','optimized-terminal'] if harness=='equivalence16::add_preweighted_shared_selector' else []
metadata=json.loads(subprocess.check_output(['cargo','+1.94.1','metadata','--offline','--format-version','1','--manifest-path',str(manifest),*features],text=True))
pkgs={p['id']:p for p in metadata['packages']};nodes=[dict(name=pkgs[n['id']]['name'],version=pkgs[n['id']]['version'],source=pkgs[n['id']]['source'],features=n['features'])for n in metadata['resolve']['nodes']]
old=json.loads((H/'features227-resume4.json').read_text())['validation']['nodes']
without=lambda ns:sorted([n for n in ns if n['name']!='pv-b3p6-reference227'],key=lambda n:(n['name'],n['version']))
if leaf:
 oldby={n['name']+n['version']:n for n in old};assert all(n==oldby[n['name']+n['version']] for n in nodes if n['name']!='pv-b3p6-reference227'), 'leaf dependency features differ'
else:assert without(nodes)==without(old),'dependency features differ from deployed parity authority'
inputs=dict(run=label,harness=harness,timeout=seconds,revision=(R/'revision').read_text().strip(),prefixes=prefixes,nodes=nodes,profile=dict(opt_level=3,debug_assertions=False,overflow_checks=False),KMX_patch_sha256='bcdf749b78eb6143789500d98d64ec3d407b8a17a6d1290c70c822473e8e9a67',KMX_stubs_sha256=sha(P/'kmx/KMX_stubs.rs'),harness_sha256=sha(P/'v244/equivalence16.rs'),source_hashes={str(p.relative_to(H/'source')):sha(p) for p in (P/'v244').glob('*.rs')},manifest_sha256=sha(manifest),leaf_manifest=leaf,tool_version=subprocess.check_output(['kani','--version'],text=True),cbmc_version=subprocess.check_output(['/home/dombarker/.kani/kani-0.67.0/bin/cbmc','--version'],text=True),rustc=subprocess.check_output(['rustc','+1.94.1','-vV'],text=True),overflow_mode='Kani requires compiler overflow instrumentation; --no-overflow-checks selects release wrapping semantics; K72100 pre-codegen refusal recorded',callee_stubs=([dict(callee='aspis_core::field::QM31::mul',binding='SHARED-CALLEES.json')] if any(w in harness for w in ['equality_value','full_round','shared_']) else [])+([dict(callee='aspis_core::field::QM31::square',binding='SHARED-CALLEES.json')] if 'full_round' in harness else []),function_pointer_quarantine=False,expected_time='optimized compilation then one named control/index equivalence SAT gate; no chained multiplication gate')
(R/(label+'-inputs.json')).write_text(json.dumps(inputs,indent=2)+'\n')
cmd=['timeout',str(seconds),'taskset','--cpu-list','0-3','cargo','kani','--manifest-path',str(manifest),'--lib','--no-overflow-checks','--exact','--harness',harness,'--solver','kissat','--output-format','terse','-j','4','-Z','unstable-options','-Z','stubbing',*features,'--cbmc-args','--unwinding-assertions']
status=run('resume16/'+label,cmd,inputs['expected_time'],{'RUSTFLAGS':'-C opt-level=3 -C debug-assertions=no','CARGO_PROFILE_DEV_OPT_LEVEL':'3','CARGO_PROFILE_DEV_DEBUG_ASSERTIONS':'false','CARGO_PROFILE_DEV_OVERFLOW_CHECKS':'true','TMPDIR':str(H/'tmp'),'PV_REV':inputs['revision']})
if not (R/label/'receipt/receipt.json').exists():raise SystemExit(status)
print((R/label/'receipt/stdout.log').read_text()[-1800:]);print((R/label/'receipt/stderr.log').read_text()[-1000:]);raise SystemExit(status)
