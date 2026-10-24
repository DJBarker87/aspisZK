#!/usr/bin/env python3
"""Configure actual-source stage glue extraction; no source transformation."""
from pathlib import Path
import subprocess,json
B=Path(__file__).resolve().parent
H='/home/dombarker/project-offloads/codex-cx-verifier-top-20261023'
old=json.loads((B.parent/'s2w-20261023/charon-003.json').read_text())
c=[old['command'][0],'cargo','--preset','aeneas','--mir','built','--sysroot','default']
for n in ['crate','aspis_core','aspis_statement']:c+=['--opaque',n]
roots=['crate::verifier::candidate::'+n for n in ['tx1','tx2_common','tx2_authenticated']]
for n in roots:c+=['--include',n,'--start-from',n]
layouts=['crate::verifier::'+n for n in ['Prepared','Accumulator','BatchedWeights','QueryGeometry','View','Error','Phase']]
layouts+=['crate::transport::Variant','aspis_core::field::M31','aspis_core::field::CM31','aspis_core::field::QM31','aspis_core::field::WideExact','aspis_core::circle::SecureCirclePoint','aspis_statement::pool_v1::pair_forest_semantic_terminal::r0::Public','core::result::Result','core::option::Option']
for n in layouts:c+=['--include',n]
c+=['--consts','initializers','--dest-file',H+'/VTop_Stages.llbc','--','--manifest-path',H+'/src/crates/aspis-r1-cost-probe/Cargo.toml','--locked','--offline','--release','--lib','--jobs','1']
x={**old,'attempt':'charon-001','source_revision':subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),'command':c,'sources':['src/'+n for n in ['Cargo.toml','Cargo.lock','crates/aspis-r1-cost-probe/Cargo.toml','crates/aspis-r1-cost-probe/src/candidate.rs','crates/aspis-r1-cost-probe/src/verifier.rs']],'deps_fingerprint':{'overlay':'host-overlay.json','scope':'All tracked Rust and Cargo inputs overlaid from this revision; private copied warm cache. Only three stage roots transparent; cone bodies opaque.'},'expected_time':'Optimized cached Rust compilation and stage-entry MIR extraction; no arithmetic generation or elimination','timeout':300}
x['env']['CARGO_TARGET_DIR']=H+'/charon-target'
(B/'charon-001.json').write_text(json.dumps(x,indent=2)+'\n')
