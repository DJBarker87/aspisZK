#!/usr/bin/env python3
"""Render PCQG_Exxx_spec.json for the NDE reference-crate re-extractions (overflow checks ON). Usage: PCQG_make_nde_specs.py <run> <2|5>"""
import json,sys,hashlib
from pathlib import Path
E=Path(__file__).resolve().parent
HOST='/home/dombarker/project-offloads/codex-pc-prov-p1f-20261109'
TOOL='/home/dombarker/project-offloads/codex-cx-extraction-repro1-20261027/XRa_bin'
AE='/home/dombarker/project-offloads/codex-pc-prov-p4c-20261109/PCWC_T001_out/work/bin/aeneas'
run,n=sys.argv[1:3]
cfg={'2':dict(ns='NDE_Reference2',roots=['crate::lift_ref','crate::extension_limbs_ref','crate::extension_raw_ref'],src='PCQG_NDE_reference2.rs',nml='NML_E012'),
     '5':dict(ns='NDE_Reference5',roots=['crate::link_weight_ref'],src='PCQG_NDE_reference5.rs',nml='NML_E006')}[n]
out=f'{HOST}/{run}_emitted'
ch=[f'{TOOL}/charon','cargo','--preset','aeneas','--mir','built','--sysroot','default','--include','core::option::Option','--include','core::result::Result','--include','core::option::_::ok_or']
for r in cfg['roots']:ch+=['--start-from',r]
ch+=['--dest-file',f'{out}/repro.llbc','--','--manifest-path',f'{out}/crate/Cargo.toml','--offline','--release','--lib','--jobs','1']
ae=[AE,'-sequential','-no-progress-bar','-abort-on-error','-backend','lean','-namespace',cfg['ns'],'-dest',f'{out}/raw','-subdir',cfg['ns'],'-split-files',f'{out}/repro.llbc']
man='[package]\nname="nde_reference"\nversion="0.1.0"\nedition="2021"\n[workspace]\n'
d=dict(run=run,spec_id='NDE'+n,label=f'{cfg["ns"]} re-extraction, overflow checks ON (P1f)',charon_command=ch,aeneas_command=ae,source_file=cfg['src'],
 reference_sha256=hashlib.sha256((E/cfg['src']).read_bytes()).hexdigest(),manifest_sha256=hashlib.sha256(man.encode()).hexdigest(),namespace=cfg['ns'],start_from=cfg['roots'],configuration=dict(start_from=cfg['roots'],include=[],opaque=[],features='(standalone crate, no features)',manifest='generated nde_reference/Cargo.toml',namespace=cfg['ns'],crate='nde_reference'),covers=dict(modules=[cfg['ns']+'.Funs']),extra_env={'CARGO_PROFILE_RELEASE_OVERFLOW_CHECKS':'true','RUSTFLAGS':'-C overflow-checks=yes'},
 expected_limits={'memory.high':'3221225472','memory.max':'4294967296','memory.swap.max':'0','pids.max':'64'},
 p1f=dict(basis='PCVA_CLASSIFICATION CONFIG_MISMATCH: gate checked (overflow ON); P5 fresh emission %s was overflow OFF; same source and manifest, original Aeneas, overflow checks ON'%cfg['nml'],
  differences_from_P5_emission='Aeneas = rebuilt original b59d5188 (959659a6...) not b59d5188-extended; overflow checks ON; no -diagnose-translation (as NML); crate staged by PCQG_nde.py, no NHR frozen payload (standalone crate as in NML)'))
(E/(run+'_spec.json')).write_text(json.dumps(d,indent=1)+'\n');print(run+'_spec.json')
