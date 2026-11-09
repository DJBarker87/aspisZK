#!/usr/bin/env python3
"""Render one entry of PCO_extract_specs.json into a runnable <run>_spec.json for PCO_extract.py.
Usage: python3 PCO_render_spec.py S001 PCO_E001 [--namespace NS]
The charon/aeneas argument shape is the one used by NMH_E018/NMH_E001 (NHR extractor): fixed core includes, one or more
--start-from roots, entry --include/--opaque lists, dest llbc under <run>_emitted, cargo args `--locked --offline --release
--lib --jobs 1 --features F`. Only frozen-kind specs are runnable (reference and cut kinds are routed to P4)."""
import json,sys,subprocess,os
from pathlib import Path
E=Path(__file__).resolve().parent
HOST=os.environ.get('PCO_HOST_BASE','/home/dombarker/project-offloads/codex-pc-prov-p0-20261109')
TOOL='/home/dombarker/project-offloads/codex-cx-extraction-repro1-20261027/XRa_bin'
REV='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387'
def render(s,run,host=HOST,namespace=None):
 assert s['kind']=='frozen',('only frozen specs are runnable',s['spec_id'],s['kind'])
 ns=namespace or s['namespace']
 out=f'{host}/{run}_emitted'
 ch=[f'{TOOL}/charon','cargo','--preset','aeneas','--mir','built','--sysroot','default','--include','core::option::Option','--include','core::result::Result','--include','core::option::_::ok_or']
 for r in s['start_from']:ch+=['--start-from',r]
 for i in s.get('include',[]):ch+=['--include',i]
 for o in s.get('opaque',[]):ch+=['--opaque',o]
 ch+=['--dest-file',f'{out}/repro.llbc','--','--manifest-path',f'{host}/PCO_workspace/{s["manifest"]}','--locked','--offline','--release','--lib','--jobs','1','--features',s['features']]
 ae=[f'{TOOL}/aeneas-b59d5188-extended','-diagnose-translation','-sequential','-no-progress-bar','-abort-on-error','-backend','lean','-namespace',ns,'-dest',f'{out}/raw','-subdir',ns,'-split-files',f'{out}/repro.llbc']
 tree=subprocess.check_output(['git','rev-parse',REV+'^{tree}'],cwd=E,text=True).strip()
 return dict(run=run,spec_id=s['spec_id'],label=s.get('label',''),charon_command=ch,aeneas_command=ae,opacity=[],
  configuration=dict(start_from=s['start_from'],include=s.get('include',[]),opaque=s.get('opaque',[]),features=s['features'],manifest=s['manifest'],namespace=ns,crate=s['crate']),
  covers=s.get('covers'),p1_half=s.get('p1_half'),frozen_revision=REV,frozen_source_tree_git_hash=tree,
  expected_limits={'memory.high':'3221225472','memory.max':'4294967296','memory.swap.max':'0','pids.max':'64'},
  basis=s.get('basis','Frozen-source extraction with the pinned NHR stager, Charon and Aeneas; no inferred opacity.'))
if __name__=='__main__':
 sid,run=sys.argv[1:3];ns=sys.argv[sys.argv.index('--namespace')+1] if '--namespace' in sys.argv else None
 specs={x['spec_id']:x for x in json.loads((E/'PCO_extract_specs.json').read_text())['specs']}
 d=render(specs[sid],run,namespace=ns);(E/(run+'_spec.json')).write_text(json.dumps(d,indent=1)+'\n');print(run+'_spec.json')
