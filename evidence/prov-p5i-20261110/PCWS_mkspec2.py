#!/usr/bin/env python3
"""PCWS_mkspec2.py RUN NAMESPACE SRC_SPEC.json [--off] : clone roots/include/opaque/features of an archived frozen-4bb3b3f spec (SRC_SPEC) into a PCWS spec
using the PCWS_mkspec.py shape (NMH_E021 head, cargo --jobs 4 + CARGO_BUILD_JOBS=4, stable --dest-file, original Aeneas 959659a6, opacity [] to the stager).
Difference from PCWS_mkspec.py: reads roots, --include and --opaque selectors from a source spec, and --off selects overflow-checks OFF."""
import json,sys,subprocess
sys.dont_write_bytecode=True
run,ns,src=sys.argv[1:4]; OFF='--off' in sys.argv
HOST='/home/dombarker/project-offloads/codex-pc-prov-p5i-20261110'
ORIG='/home/dombarker/project-offloads/codex-pc-prov-p4c-20261109/PCWC_T001_out/work/bin/aeneas'
s=json.load(open(src)); cf=s['configuration']
roots=cf['roots']; inc=cf['include']; opq=cf['opaque']; feat=cf['features'] if isinstance(cf['features'],str) else ','.join(cf['features']); crate=cf.get('crate','aspis-r1-cost-probe')
d=json.load(open('../emission-repro-20261110/NMH_E021_spec.json'))
c=d['charon_command']; head=c[:c.index('--start-from')]
for x in inc: head+=['--include',x]
nc=head
for r in roots: nc+=['--start-from',r]
for o in opq: nc+=['--opaque',o]
nc+=['--dest-file',HOST+'/'+run+'_repro.llbc','--','--manifest-path',HOST+'/PCWS_workspace/crates/'+crate+'/Cargo.toml','--locked','--offline','--release','--lib','--jobs','4','--features',feat]
ae=[ORIG,'-diagnose-translation','-sequential','-no-progress-bar','-backend','lean','-namespace',ns,'-dest',HOST+'/'+run+'_emitted/raw','-subdir',ns,'-split-files',HOST+'/'+run+'_emitted/repro.llbc']
for k in ('groups','members','bytes','basis','diagnostic_only'): d.pop(k,None)
d.update(run=run,spec_id=run,label='PCWS '+run,charon_command=nc,aeneas_command=ae,aeneas_tool='original',opacity=[],
 expected_limits={'memory.high':'3221225472','memory.max':'4294967296','memory.swap.max':'0','pids.max':'64'},
 extra_env=({'CARGO_BUILD_JOBS':'4'} if OFF else {'CARGO_PROFILE_RELEASE_OVERFLOW_CHECKS':'true','RUSTFLAGS':'-C overflow-checks=yes','CARGO_BUILD_JOBS':'4'}),
 configuration_overflow_checks=('OFF' if OFF else 'ON'),frozen_revision='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387',
 pin_note='cargo --jobs 4, CARGO_BUILD_JOBS=4, rustc -Zthreads 1; identity by class receipt PCWE_E003',
 aeneas_sha256='959659a6aafc6a6a975b4dc67ee9d779a269b988bd44b3b31a77cf023b1709e3')
d['frozen_source_tree_git_hash']=subprocess.check_output(['git','rev-parse',d['frozen_revision']+'^{tree}'],text=True,cwd='/Users/dominic/ZK').strip()
d['configuration']=dict(start_from=roots,roots=roots,include=inc,opaque=opq,features=feat,manifest='crates/'+crate+'/Cargo.toml',namespace=ns,crate=crate)
json.dump(d,open(run+'_spec.json','w'),indent=1); print(run+'_spec.json',len(nc))
