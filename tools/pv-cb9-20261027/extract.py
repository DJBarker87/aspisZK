"""Direct shipped roots, unchanged pinned tools, fail-closed sequential scopes."""
from pathlib import Path
import subprocess, json, shlex, hashlib, sys, re
root=Path(__file__).resolve().parents[2]; out=root/'evidence/pv-cb9-20261027'
base='/home/dombarker/project-offloads/codex-pv-cb3-20261026'
pins='/home/dombarker/project-offloads/codex-pv-cb-20261026/pinned-tools'
gate='/home/dombarker/project-offloads/codex-cx-prover-rw-20261023/src/tools/prover-rw-20261023/native-entropy'
entries={226:('aspis_statement::pool_v1::pair_forest_semantic_terminal::r0::Public::public_bytes','aspis_statement::pool_v1::pair_forest_semantic_terminal::*+aspis_core::state_only_prefix::*+aspis_statement::pool_v1::pair_tree_profile::*'),227:('aspis_statement::pool_v1::pair_forest_semantic_terminal::r0::Public::terminal_qm31','aspis_statement::pool_v1::pair_forest_semantic_terminal::*+aspis_core::state_only_prefix::*'),228:('aspis_statement::pool_v1::pair_forest_trace::build_pool_v1_pair_forest_copy_registry_v1','aspis_statement::pool_v1::pair_forest_trace::*'),230:('aspis_statement::state_only_semantic::state_only_copy_helper_sum','aspis_statement::state_only_semantic::*'),250:('aspis_r1_cost_probe::sampler::ordinary_sample','aspis_r1_cost_probe::sampler::*'),251:('aspis_r1_cost_probe::weights::Weights::materialize','aspis_r1_cost_probe::weights::*'),252:('aspis_r1_cost_probe::weights::Weights::new','aspis_r1_cost_probe::weights::*'),254:('aspis_r1_cost_probe::weights::powers','aspis_r1_cost_probe::weights::powers')}
def ssh(c): return subprocess.run(['ssh','dombarker@100.108.41.90',c],text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
op=int(sys.argv[1]);stage=sys.argv[2];entry,inc=entries[op];assert stage in ('charon','aeneas')
variant=sys.argv[3] if len(sys.argv)>3 else ''
assert variant in ('','current')
if variant:
 assert op==252
 entry='pv_cb3_source::current_weights::Weights::new';inc='pv_cb3_source::current_weights::*'
# Check each sibling immediately before every operation.
r=subprocess.run(['git','grep','-n',f'op{op}_source','codex/pv-cb-20261026','codex/pv-cb3-20261026','codex/pv-cbmid-20261027','codex/pv-cblib-20261027','--','*.lean'],cwd=root,text=True,capture_output=True)
(out/f'op{op}-siblings.txt').write_text(r.stdout+r.stderr); assert r.returncode==1, 'SKIP(sibling) or grep failure'
name=f'cb9-op{op}{variant}-{stage}';d=out/name
if d.exists():
 assert (d/'refusal.json').exists(), 'Never rerun a completed extraction unchanged'
 old=json.loads((d/'refusal.json').read_text());assert not old['charged']
 import time
 left=(d/'refusal.json').stat().st_mtime+180-time.time()
 assert left<=0, f'Reservation cooldown: {left:.1f} seconds remain'
 archive=d.with_name(name+'-refusal-'+str(len(list(out.glob(name+'-refusal-*')))+1));d.rename(archive)
d.mkdir();remote=base+'/'+name
revision=subprocess.check_output(['git','rev-parse','HEAD'],cwd=root,text=True).strip()
quiet="import pathlib,json,time; p=pathlib.Path('/home/dombarker/project-offloads/QUIET_WINDOW.json'); u=float(json.loads(p.read_text()).get('until',0)) if p.exists() else 0; print('quiet until',u); raise SystemExit(78 if time.time()<u else 0)"
r=ssh(f'mkdir -p {remote}; python3 -c {shlex.quote(quiet)} > {remote}/reservation.log 2>&1 && python3 {gate}/reservation.py {remote}/admission-before.json >> {remote}/reservation.log 2>&1; result=$?; cat {remote}/reservation.log; exit $result');(d/'reservation.log').write_text(r.stdout)
if r.returncode: (d/'refusal.json').write_text(json.dumps(dict(exit=r.returncode,charged=False,reason=r.stdout)));sys.exit(r.returncode)
namespace=f'PV_CB3_CB9Op{op}{variant.title()}';llbc=base+'/'+namespace+'.llbc';generated=base+f'/cb9-op{op}{variant}-generated'
if stage=='charon':
 args=['timeout','120','env','PATH=/home/dombarker/.cargo/bin:/usr/local/bin:/usr/bin:/bin','RUSTUP_TOOLCHAIN=nightly-2026-06-01','RUSTFLAGS=--cfg pv_cb_extract',f'CARGO_TARGET_DIR={base}/charon-target',pins+'/charon','cargo','--preset','aeneas','--mir','built','--rustc-arg=--cfg=kani','--rustc-arg=--cfg=pv_cb_extract','--sysroot','default','--start-from',entry]
 for pattern in (inc+'+aspis_core::field::*').split('+'):args+=['--include',pattern]
 args+=['--dest-file',llbc,'--','--manifest-path',base+'/source-proof/Cargo.toml','--release','--offline','--lib','--jobs','4']
else:
 assert ssh('mkdir -p '+generated).returncode==0
 args=['timeout','120',pins+'/aeneas','-sequential','-no-progress-bar','-abort-on-error','-strict-joins','-backend','lean','-namespace',namespace,'-dest',generated,'-split-files','-emit-json',llbc]
target=dict(target=args,entry=entry,source_revision=revision,expected_phase='optimized compilation and direct shipped MIR extraction' if stage=='charon' else 'symbolic extraction; preflight enabled',limits=dict(MemoryHigh='6G',MemoryMax='8G',MemorySwapMax=0,TasksMax=64),print_axioms='N/A extraction; no theorem claimed')
(d/'target.json').write_text(json.dumps(target,indent=2)+'\n')
cmd=['systemd-run','--user','--scope','-p','MemoryHigh=6G','-p','MemoryMax=8G','-p','MemorySwapMax=0','-p','TasksMax=64','python3',gate+'/barrier.py',remote+'/admission-barrier.json','/usr/bin/time','-v','-o',remote+'/time.log',*args]
r=ssh(shlex.join(cmd)+' > '+remote+'/output.log 2>&1');(d/'transport.log').write_text(r.stdout)
code='''import pathlib,json,hashlib
p=pathlib.Path(%r)
r={'logs':{q.name:q.read_text() for q in p.iterdir() if q.suffix in ('.log','.json')},'hashes':{}}
for n in %r:
 q=pathlib.Path(n)
 if q.is_file():r['hashes'][n]={'sha256':hashlib.sha256(q.read_bytes()).hexdigest(),'size':q.stat().st_size}
print(json.dumps(r))
'''%(remote,[llbc,pins+'/aeneas',pins+'/charon',base+'/source-proof/lib.rs',base+'/source-proof/Cargo.toml',generated+'/Funs.lean',generated+'/Types.lean'])
s=json.loads(ssh('python3 -c '+shlex.quote(code)).stdout)
for n,v in s['logs'].items():(d/n).write_text(v)
t=s['logs'].get('time.log','')
def m(k):
 a=re.search(re.escape(k)+r':\s*(.+)',t);return a[1] if a else None
target.update(exit=m('Exit status'),transport_exit=r.returncode,wall=m('Elapsed (wall clock) time (h:mm:ss or m:ss)'),peak_rss_kib=m('Maximum resident set size (kbytes)'),swap=m('Swaps'),hashes=s['hashes'])
(d/'receipt.json').write_text(json.dumps(target,indent=2)+'\n');print(name,json.dumps({k:target[k] for k in ('exit','wall','peak_rss_kib','swap')}));print(s['logs'].get('output.log','')[-4500:] if stage=='aeneas' else 'Full Charon log retained');sys.exit(r.returncode)
