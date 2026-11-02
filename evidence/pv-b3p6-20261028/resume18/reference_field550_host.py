"""Focused reference replay to bind Kani's exact bodies to the existing emission.
One capped scope per module; unchanged ae1-2 translator; no generated edits.
"""
from pathlib import Path
import sys,json,hashlib,subprocess,os
from run import H,run
ident=int(sys.argv[1]);group=sys.argv[2]
assert (ident,group) in [(79168,'prepared')]
R=H/'resume18';O=R/('reference-'+group);P=H/'source/tools/pv-b3p6-20261028/v244'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
if '--inside' not in sys.argv:
 assert not (R/f'N{ident}').exists();O.mkdir(exist_ok=False)
 command=['python3',str(Path(__file__)),str(ident),group,'--inside']
 raise SystemExit(run('resume18/N'+str(ident),command,'optimized MIR extraction and translation of exact reference '+group+' bodies; no arithmetic elimination',{'RUSTUP_TOOLCHAIN':'nightly-2026-06-01','CARGO_TARGET_DIR':str(H/'charon-target'),'CARGO_PROFILE_RELEASE_OPT_LEVEL':'3','CARGO_PROFILE_RELEASE_DEBUG_ASSERTIONS':'false','CARGO_PROFILE_RELEASE_OVERFLOW_CHECKS':'false'}))
c=Path('/home/dombarker/project-offloads/codex-pv-extract-20261027/charon');a=Path('/home/dombarker/project-offloads/codex-pv-cx-20261029/resume-ae1/pinned-tools/aeneas-ae1-2-fda587d2')
assert sha(c)=='daad69bea1114042a2d2fbd3dfde99922b152d4f57023bf8edb83e5a6f336af8'
assert sha(a)=='fda587d25a66604a973bbc2947a4416ba373b56dd8c98655991c1b6eaa240b68'
manifest=P/'Cargo.toml'
meta=json.loads(subprocess.check_output(['/home/dombarker/.cargo/bin/cargo','+1.94.1','metadata','--manifest-path',str(manifest),'--offline','--locked','--format-version','1'],text=True))
pkgs={p['id']:p for p in meta['packages']};nodes=[dict(name=pkgs[n['id']]['name'],version=pkgs[n['id']]['version'],source=pkgs[n['id']]['source'],features=n['features'])for n in meta['resolve']['nodes']]
authority=json.loads((H/'features227-resume4.json').read_text())['validation']['nodes']
strip=lambda ns:sorted([n for n in ns if n['name']!='pv-b3p6-reference227'],key=lambda n:(n['name'],n['version']))
assert strip(nodes)==strip(authority)
roots={'leading':['leading_pair_packed'],'copy':['Selectors::active_literal','pattern_values_literal'],'schedule':['add_schedule_lanes','path_lanes_literal','public_digest_lanes','add_value_lanes'],'packed':['external_linear_packed'],'prepared':['qm31_sum_products3_prepared']}[group]
module={'leading':'reference_poseidon','copy':'reference_copy_terminal','schedule':'reference_terminal','packed':'reference_poseidon','prepared':'reference_field'}[group]
llbc=O/'Reference550.llbc';gen=O/'generated';gen.mkdir()
cmd=['timeout','300','taskset','--cpu-list','0-3',str(c),'cargo','--preset','aeneas','--mir','optimized','--sysroot','default']
for n in roots:cmd+=['--start-from','crate::'+module+'::'+n]
for n in ['reference_terminal','reference_poseidon','reference_field','host_terminal_field']:
 cmd+=['--include','pv_b3p6_reference227::'+n+'::*']
for n in ['aspis_core::*','aspis_statement::poseidon2::*','aspis_statement::pool_v1::pair_tree_profile::*']:cmd+=['--include',n]
cmd+=['--dest-file',str(llbc),'--','--manifest-path',str(manifest),'--release','--locked','--offline','--lib','--jobs','4']
inputs=dict(command=cmd,roots=roots,charon_sha256=sha(c),aeneas_sha256=sha(a),translator_identity='functionally identical rebuild (ae1-2)',source_revision=(R/'harness-revision').read_text().strip(),sources={str(p.relative_to(H/'source')):sha(p)for p in P.glob('*.rs')},features=nodes,profile=dict(opt_level=3,debug_assertions=False,overflow_checks=False),lock_sha256=sha(P/'Cargo.lock'),extractor_toolchain='nightly-2026-06-01',deployed_toolchain='1.94.1',std_boundary='x-prime: use pinned source parity/structural dossier, V370 retained')
(O/'inputs.json').write_text(json.dumps(inputs,indent=2)+'\n')
with (O/'charon.log').open('w')as f:status=subprocess.run(cmd,stdout=f,stderr=subprocess.STDOUT).returncode
assert status==0,('Charon refusal',status)
assert not json.loads(llbc.read_text()).get('has_errors',False)
cmd=['timeout','300',str(a),'-sequential','-no-progress-bar','-abort-on-error','-strict-joins','-backend','lean','-namespace','PV_B3P_Reference550227','-dest',str(gen),'-split-files','-emit-json',str(llbc)]
with (O/'aeneas.log').open('w')as f:status=subprocess.run(cmd,stdout=f,stderr=subprocess.STDOUT).returncode
(O/'outputs.json').write_text(json.dumps(dict(aeneas_exit=status,command=cmd,llbc_sha256=sha(llbc),generated={p.name:dict(sha256=sha(p),bytes=p.stat().st_size)for p in gen.glob('*')if p.is_file()}),indent=2)+'\n')
raise SystemExit(status)
