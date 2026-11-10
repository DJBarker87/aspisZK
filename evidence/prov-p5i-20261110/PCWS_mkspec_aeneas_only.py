#!/usr/bin/env python3
"""PCWS_mkspec_aeneas_only.py RUN SRC_RUN [original|extended]: Aeneas-only spec on the saved LLBC of SRC_RUN (same namespace/roots/configuration)."""
import json,sys
sys.dont_write_bytecode=True
run,src,tool=sys.argv[1:4]
H='/home/dombarker/project-offloads/codex-pc-prov-p5i-20261110'
d=json.load(open(src+'_spec.json')); ns=d['configuration']['namespace']
T={'original':('/home/dombarker/project-offloads/codex-pc-prov-p4c-20261109/PCWC_T001_out/work/bin/aeneas','959659a6aafc6a6a975b4dc67ee9d779a269b988bd44b3b31a77cf023b1709e3'),
   'extended':('/home/dombarker/project-offloads/codex-cx-extraction-repro1-20261027/XRa_bin/aeneas-b59d5188-extended','c0cf4fccb0879db4ce342da991f6215732a19fc01345b9eec84e632f4673b958')}[tool]
llbc=H+'/'+src+'_repro.llbc'
d.update(run=run,spec_id=run,label='PCWS '+run,aeneas_only=True,llbc=llbc,llbc_produced_by=src+' (Charon from the same spec)',aeneas_tool=tool,aeneas_sha256=T[1],
 aeneas_command=[T[0],'-diagnose-translation','-sequential','-no-progress-bar','-backend','lean','-namespace',ns,'-dest',H+'/'+run+'_emitted/raw','-subdir',ns,'-split-files',llbc])
json.dump(d,open(run+'_spec.json','w'),indent=1); print(run,tool,ns)
