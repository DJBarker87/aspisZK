#!/usr/bin/env python3
"""Traced-run metadata for residual.py from sweep.jsonl files.
usage: runs_meta.py out.json sweep.jsonl..."""
import json, sys
out = {}
for f in sys.argv[2:]:
    for l in open(f):
        r = json.loads(l)
        if r.get('exit_status') != 0 or r.get('outcome') != 'accepted': continue
        inp = r['inputs']
        mode = 'genesis' if inp.get('zeroed_genesis_page') else r['history_mode']
        out[r['label']] = dict(kind=r['kind'], split=inp['split'], mode=mode, prefund=bool(inp.get('prefund_marker_lamports')),
                               prefund_lamports=inp.get('prefund_marker_lamports'), pairs=r['pairs'], stage1_cu=r['stage1_cu'],
                               settlement_cu=r['settlement_cu'], nested_stage2_cu=r['nested_stage2_cu'], output_lane=r.get('output_lane'))
json.dump(out, open(sys.argv[1], 'w'), indent=1); print(len(out))
