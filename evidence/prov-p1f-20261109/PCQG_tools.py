import json,hashlib
from pathlib import Path
E=Path(__file__).resolve().parent;EV=E.parent
J=lambda p:json.loads(Path(p).read_text())
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
pins=J(E/'PCQG_E001_emitted/PCQG_E001_PINS.json')
nde=J(E/'PCQG_E017_emitted/PCQG_E017_PINS.json')
files={}
for n,orig in (('PCQG_extract.py','prov-p1e-20261109/PCQF_extract.py'),('PCQG_run.py','prov-p1e-20261109/PCQF_run.py'),('PCQG_run_host.py','prov-p1e-20261109/PCQF_run_host.py'),('PCQG_render_spec.py','prov-p1e-20261109/PCQF_render_spec.py'),('PCQG_chain.sh','prov-p1e-20261109/PCQF_chain.sh'),('PCQG_STAGER_PIN.json','prov-p1e-20261109/PCQF_STAGER_PIN.json')):
    files[n]=dict(original=orig,original_sha256=sha(EV/orig),sha256=sha(E/n))
files['PCQG_extract.py']['changes']='PCQF_ -> PCQG_; adds assert that the aeneas binary sha256 equals 959659a6aafc6a6a975b4dc67ee9d779a269b988bd44b3b31a77cf023b1709e3 before the stager runs (same assert as P1d PCQE_extract.py); host base p1f'
files['PCQG_run.py']['changes']='PCQF_ -> PCQG_; host base p1f; admission: Stream C (codex-pc-*) scope count must be < 2 (was < 3), whole-host count < 6, disk >= 40 GB, reservation barrier unchanged'
files['PCQG_run_host.py']['changes']='PCQF_ -> PCQG_; no logic change'
files['PCQG_render_spec.py']['changes']='aeneas command = P4c rebuilt original path (was aeneas-b59d5188-extended); host base p1f; overflow checks ON unchanged'
files['PCQG_chain.sh']['changes']='PCQF_ -> PCQG_; host base p1f'
files['PCQG_STAGER_PIN.json']['changes']='PCQF_ -> PCQG_ in text only; stager sha256 unchanged'
files['PCQG_run_nde.py']=dict(original='PCQG_run.py',sha256=sha(E/'PCQG_run_nde.py'),changes='copy of PCQG_run.py for the standalone NDE reference crates: uploads PCQG_nde.py, the spec and the crate source instead of the NHR stager and frozen payload; same admission, caps, receipts')
files['PCQG_nde.py']=dict(original=None,sha256=sha(E/'PCQG_nde.py'),changes='new host-side controller: writes the historical nde_reference manifest (sha256 9d646324...) and source (sha256 asserted), runs Charon then Aeneas in the admitted scope with overflow checks ON, env equal to NHR_stage.py plus -C overflow-checks=yes')
files['PCQG_make_nde_specs.py']=dict(original=None,sha256=sha(E/'PCQG_make_nde_specs.py'),changes='renders NDE spec files')
tl=dict(note='P1f uses the rebuilt ORIGINAL Aeneas b59d5188 (sha256 959659a6...) in the P4c host workspace (read-only reference, asserted before every use by PCQG_extract.py / PCQG_nde.py and recorded in every PINS) and the original Charon XRa_bin/charon (daad69be, driver efdbe5b8). Every PCQG_ emission is from this tool; P2/P3 must use the gate-compatible library for PCQE_/PCQG_ emissions (as for P1d).',
 tools=pins['tools'],aeneas_path='/home/dombarker/project-offloads/codex-pc-prov-p4c-20261109/PCWC_T001_out/work/bin/aeneas',aeneas_build_record='evidence/prov-p4c-20261109/PCWC_TOOL_BUILD.json',stager_sha256=pins['stager_sha256'],
 toolchain=pins['environment'],nde_environment=nde['environment'],files=files,
 aeneas_flags='-diagnose-translation -sequential -no-progress-bar -abort-on-error -backend lean ... -split-files (frozen-source runs, as P1d/P1e); the NDE runs omit -diagnose-translation as the P5 NML runs did',
 specs_note='roots, features and opacity per PCQG_extract_specs.json (P1e specs copied unchanged plus the P1F_* and NDE entries)')
(E/'PCQG_TOOLS.json').write_text(json.dumps(tl,indent=1)+'\n')
