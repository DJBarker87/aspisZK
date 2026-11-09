#!/usr/bin/env python3
"""Overflow-checks redo spec: copy an earlier run's rendered spec unchanged except for
 run id, host base, workspace/namespace prefix (PCQ_/PCO_ -> PCQC_), and extra_env (overflow checks on).
Usage: python3 PCQC_make_spec.py <old_spec_path> <old_run> <new_run> <kind: redo|retry>
Writes <new_run>_spec.json next to this script."""
import json,sys,re
from pathlib import Path
E=Path(__file__).resolve().parent
old,oldrun,new,kind=sys.argv[1:5]
t=Path(old).read_text()
t=t.replace(oldrun,new)
t=re.sub(r'/home/dombarker/project-offloads/codex-pc-prov-p(0|1a|1b)-20261109','/home/dombarker/project-offloads/codex-pc-prov-p1c-20261109',t)
t=t.replace('PCQ_','PCQC_').replace('PCO_','PCQC_')
s=json.loads(t)
s['extra_env']={'CARGO_PROFILE_RELEASE_OVERFLOW_CHECKS':'true','RUSTFLAGS':'-C overflow-checks=yes'}
s['p1c']=dict(kind=kind,earlier_run=oldrun,earlier_spec=old,note='same spec as the earlier run except run id, host base, PCQ_/PCO_ -> PCQC_ in workspace and namespace, and overflow checks on (ruling 2026-11-09)')
(E/(new+'_spec.json')).write_text(json.dumps(s,indent=1)+'\n')
print(new+'_spec.json',s['configuration']['namespace'])
