#!/usr/bin/env python3
"""PCWJ_render_spec.py RUN KIND: clone an archived frozen-4bb3b3f extraction spec into a PCWJ spec (roots/namespace/paths changed only).
KIND slot : OFF config (no overflow-checks env), aspis-r1-cost-probe, root crate::compact::slot_offset (+ the SLOT_NODES/OFF_NODES it reads).
KIND reg  : ON config, aspis-statement, root crate::pool_v1::verifier_registry::validate_verifier_registry_entry_v2 (reaches VerifierRegistryEntryV2 and VerifierEntryStatusV1)."""
import json,sys,subprocess
sys.dont_write_bytecode=True
run,kind=sys.argv[1:3]
HOST='/home/dombarker/project-offloads/codex-pc-prov-p5a-20261110'
TOOL='/home/dombarker/project-offloads/codex-cx-extraction-repro1-20261027/XRa_bin/aeneas-b59d5188-extended'
if kind=='slot':
    d=json.load(open('../emission-repro-20261110/NMH_E010_spec.json')); ns='PCWJ_slot'
    roots=['crate::compact::slot_offset']; crate='aspis-r1-cost-probe'
    feat='private-leaf-salts,optimized-terminal,program-build'; env={}
    ov='OFF (stager default environment: no CARGO_PROFILE_RELEASE_OVERFLOW_CHECKS, no -C overflow-checks=yes)'
else:
    d=json.load(open('../prov-p1f-20261109/PCQG_E003_spec.json')); ns='PCWJ_registry'
    roots=['crate::pool_v1::verifier_registry::validate_verifier_registry_entry_v2']; crate='aspis-statement'
    feat='r0,pool-v1-kernel'; env={'CARGO_PROFILE_RELEASE_OVERFLOW_CHECKS':'true','RUSTFLAGS':'-C overflow-checks=yes'}
    ov='ON (CARGO_PROFILE_RELEASE_OVERFLOW_CHECKS=true; -C overflow-checks=yes appended to the stager RUSTFLAGS)'
c=d['charon_command']
head=c[:c.index('--start-from')] if '--start-from' in c else c[:c.index('--dest-file')]
# keep the generic option prefix up to the first --start-from, then our roots, then the tail from --dest-file with relocated paths
tail=c[c.index('--dest-file'):]
tail[1]=HOST+'/'+run+'_emitted/repro.llbc'
tail[tail.index('--manifest-path')+1]=HOST+'/PCWJ_workspace/crates/'+crate+'/Cargo.toml'
tail[tail.index('--features')+1]=feat
nc=head
for r in roots: nc+=['--start-from',r]
nc+=tail
ae=[TOOL,'-diagnose-translation','-sequential','-no-progress-bar','-abort-on-error','-backend','lean','-namespace',ns,'-dest',HOST+'/'+run+'_emitted/raw','-subdir',ns,'-split-files',HOST+'/'+run+'_emitted/repro.llbc']
d.update(run=run,spec_id='PCWJ_'+kind,label='PCWJ '+kind,charon_command=nc,aeneas_command=ae,aeneas_tool='extended',opacity=[],
 expected_limits={'memory.high':'3221225472','memory.max':'4294967296','memory.swap.max':'0','pids.max':'64'},extra_env=env,
 configuration_overflow_checks=ov,frozen_revision='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387')
d['frozen_source_tree_git_hash']=subprocess.check_output(['git','rev-parse',d['frozen_revision']+'^{tree}'],text=True).strip()
d['configuration']=dict(start_from=roots,roots=roots,include=[x for i,x in enumerate(nc) if i and nc[i-1]=='--include'],opaque=[],features=feat,manifest='crates/'+crate+'/Cargo.toml',namespace=ns,crate=crate)
for k in ('covers','supersedes','p1f','groups','members','bytes','basis'): d.pop(k,None)
json.dump(d,open(run+'_spec.json','w'),indent=1)
print(run+'_spec.json',kind,ns,len(nc))
