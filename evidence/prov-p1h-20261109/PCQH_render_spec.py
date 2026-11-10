#!/usr/bin/env python3
"""Render one entry of PCQH_extract_specs.json into PCQH_Exxx_spec.json (P1e). Same charon/aeneas argument shape as
PCQ_render_spec.py / PCQC_make_spec.py; overflow checks OFF (ruling: Stream A lead, wrapping-configuration gate bodies).
Usage: python3 PCQH_render_spec.py <spec_id> <run> [<attempt_note>]"""
import json,sys,subprocess
from pathlib import Path
sys.dont_write_bytecode=True
E=Path(__file__).resolve().parent
HOST='/home/dombarker/project-offloads/codex-pc-prov-p1h-20261109'
TOOL='/home/dombarker/project-offloads/codex-cx-extraction-repro1-20261027/XRa_bin'
REV='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387'
def render(s,run,note=None,overrides=None):
 s=dict(s,**(overrides or {}))
 ns=s['namespace'];out=f'{HOST}/{run}_emitted'
 ch=[f'{TOOL}/charon','cargo','--preset','aeneas','--mir','built','--sysroot','default','--include','core::option::Option','--include','core::result::Result','--include','core::option::_::ok_or']
 for r in s['start_from']:ch+=['--start-from',r]
 for i in s.get('include',[]):ch+=['--include',i]
 for o in s.get('opaque',[]):ch+=['--opaque',o]
 ch+=['--dest-file',f'{out}/repro.llbc','--','--manifest-path',f'{HOST}/PCQH_workspace/{s["manifest"]}','--locked','--offline','--release','--lib','--jobs','1','--features',s['features']]
 aep={'original':'/home/dombarker/project-offloads/codex-pc-prov-p4c-20261109/PCWC_T001_out/work/bin/aeneas','extended':f'{TOOL}/aeneas-b59d5188-extended'}[s.get('aeneas_tool','extended')]
 ae=[aep,'-diagnose-translation','-sequential','-no-progress-bar','-abort-on-error','-backend','lean','-namespace',ns,'-dest',f'{out}/raw','-subdir',ns,'-split-files',f'{out}/repro.llbc']
 tree=subprocess.check_output(['git','rev-parse',REV+'^{tree}'],cwd=E,text=True).strip()
 return dict(run=run,spec_id=s['spec_id'],aeneas_tool=s.get('aeneas_tool','extended'),label=s.get('label',''),charon_command=ch,aeneas_command=ae,opacity=[],
  configuration=dict(start_from=s['start_from'],include=s.get('include',[]),opaque=s.get('opaque',[]),features=s['features'],manifest=s['manifest'],namespace=ns,crate=s['crate']),
  covers=s.get('covers'),supersedes=s.get('supersedes'),frozen_revision=REV,frozen_source_tree_git_hash=tree,
  expected_limits={'memory.high':'3221225472','memory.max':'4294967296','memory.swap.max':'0','pids.max':'64'},
  extra_env={},configuration_overflow_checks='OFF (stager default environment: no CARGO_PROFILE_RELEASE_OVERFLOW_CHECKS, no -C overflow-checks=yes)',
  p1g=dict(note=note or '',basis=s.get('basis')))
if __name__=='__main__':
 sid,run=sys.argv[1:3];note=sys.argv[3] if len(sys.argv)>3 else None
 specs={x['spec_id']:x for x in json.loads((E/'PCQH_extract_specs.json').read_text())['specs']}
 ov=json.loads((E/'PCQH_overrides.json').read_text()).get(run) if (E/'PCQH_overrides.json').exists() else None
 d=render(specs[sid],run,note,ov);(E/(run+'_spec.json')).write_text(json.dumps(d,indent=1)+'\n');print(run+'_spec.json')
