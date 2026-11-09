#!/usr/bin/env python3
"""Run inside one capped scope: declaration-level comparison of already-rebuilt objects that are
not byte-identical to their overlay objects (built before per-module comparison was enabled).
argv: input tsv (module, overlay, replay), output jsonl. One L187_Compare process per module."""
import sys,subprocess,json,pathlib
W=pathlib.Path(__file__).resolve().parent
inp,outp=sys.argv[1],sys.argv[2]
with open(outp,'w') as o:
  for k,line in enumerate(open(inp)):
    t=W/'tmp'/('retro_%d.tsv'%k); j=W/'tmp'/('retro_%d.jsonl'%k); t.write_text(line)
    r=subprocess.run(['timeout','120',str(W/'tools'/'L187_Compare'),str(t),str(j)],capture_output=True,text=True)
    try: row=json.loads(j.read_text().splitlines()[0])
    except Exception: row=dict(module=line.split('\t')[0],error='exit %d %s'%(r.returncode,r.stderr[-300:]))
    o.write(json.dumps(row)+'\n'); o.flush()
    for x in (t,j):
      if x.is_file(): x.unlink()
