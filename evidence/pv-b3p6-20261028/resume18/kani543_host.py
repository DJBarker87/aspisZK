"""One static-free refused-function gate per scope, controls before positives."""
from run import H,run
from pathlib import Path
import sys,json,hashlib,subprocess,re,os
os.environ["PATH"]="/home/dombarker/.cargo/bin:/usr/bin:/bin"
ident=int(sys.argv[1]);assert 79100<=ident<=79103
names=['raw_all_words_wrong','raw_all_words','internal_all_words_wrong','internal_all_words']
name=names[ident-79100];control=ident%2==0;seconds=180
R=H/'resume18';label=f'K{ident}';assert not any(R.glob(label+'*')),'never reuse any existing ID'
assert len(list(R.glob('K*/receipt/receipt.json')))<30
if not control:
 p=R/f'K{ident-1}/receipt';assert json.loads((p/'receipt.json').read_text())['exit_status']!=0
 log=(p/'stdout.log').read_text();assert 'VERIFICATION:- FAILED' in log and 'assertion' in log.lower(),log[-2500:]
P=H/'source/tools/pv-b3p6-20261028';manifest=P/'v244-k3-17/Cargo.toml';sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
for n in ['equivalence_k3_17.rs','equivalence_helpers_k3_17.rs','lib_k3_17.rs','equivalence18.rs']:
 s=(P/'v244'/n).read_text();assert not re.search(r'static\s+mut|thread_local!|Atomic\w*|(?:Ref|Unsafe)?Cell|Mutex|Once(?:Cell|Lock)|shared_callee16',s)
assert sha(P/'kmx/KMX_stubs.rs')=='ad8efb63d8ff791274c91eff9ccc5b9fb126f5a3ac7f27aa811ca11b8e25c138'
for x in json.loads((H/'resume17/verbatim-prefixes.json').read_text()):
 p=H/'source'/x['path'];q=H/'source'/x['prefix_source'];assert sha(p)==x['module_sha256'] and sha(q)==x['prefix_sha256'] and p.read_bytes()[:x['prefix_bytes']]==q.read_bytes()
metadata=json.loads(subprocess.check_output(['cargo','+1.94.1','metadata','--offline','--locked','--format-version','1','--manifest-path',str(manifest)],text=True))
packages={p['id']:p for p in metadata['packages']};nodes=[dict(name=packages[n['id']]['name'],version=packages[n['id']]['version'],source=packages[n['id']]['source'],features=n['features'])for n in metadata['resolve']['nodes']]
old=json.loads((H/'features227-resume4.json').read_text())['validation']['nodes'];by={(n['name'],n['version']):n for n in old}
assert all(n==by[n['name'],n['version']]for n in nodes if n['name']!='pv-b3p6-reference227')
inputs=dict(run=label,harness='equivalence18::'+name,matched_control=('equivalence18::'+name+'_wrong')if not control else 'this is the matched mutation; xor one output bit',control_run=f'K{ident-1}'if not control else None,timeout=seconds,revision=(H/'resume17/revision').read_text().strip(),harness_revision=(R/'harness-revision').read_text().strip(),source_hashes={str(p.relative_to(H/'source')):sha(p)for p in (P/'v244').glob('*.rs')},manifest_sha256=sha(manifest),nodes=nodes,profile=dict(opt_level=3,debug_assertions=False,overflow_checks=False),source_change='dedicated harness crate with no shared oracle module; removed unused mul/square stubs; new wider input domain; historical named gates retained unchanged',KMX_patch_sha256='bcdf749b78eb6143789500d98d64ec3d407b8a17a6d1290c70c822473e8e9a67',KMX_stubs_sha256=sha(P/'kmx/KMX_stubs.rs'),domain='all u32 field limb representations, no canonicality assumption; fixed arrays of 4 or 16',expected_time='optimized compilation followed by named raw/internal equivalence SAT gate; no multiplication chain',actual_kani_compiler=subprocess.check_output(['/home/dombarker/.kani/kani-0.67.0/bin/kani-compiler','--version'],text=True))
(R/(label+'-inputs.json')).write_text(json.dumps(inputs,indent=2)+'\n')
tmp=R/(label+'-tmp');tmp.mkdir()
cmd=['timeout',str(seconds),'taskset','--cpu-list','0-3','cargo','kani','--manifest-path',str(manifest),'--lib','--no-overflow-checks','--exact','--harness',inputs['harness'],'--solver','kissat','--output-format','terse','-j','4','-Z','unstable-options','-Z','stubbing','--cbmc-args','--unwinding-assertions']
status=run('resume18/'+label,['python3',str(H/'kani_inner227_resume18_host.py'),str(ident),'--',*cmd],inputs['expected_time'],{'RUSTFLAGS':'-C opt-level=3 -C debug-assertions=no','CARGO_PROFILE_DEV_OPT_LEVEL':'3','CARGO_PROFILE_DEV_DEBUG_ASSERTIONS':'false','CARGO_PROFILE_DEV_OVERFLOW_CHECKS':'true','TMPDIR':str(tmp),'PV_REV':inputs['revision']})
print(json.dumps(dict(run=label,exit=status,control=control)),flush=True)
raise SystemExit(status)
