"""Tiny integer-table audit, not a Lean/Rust/source-refinement proof."""
from pathlib import Path
import re,json,hashlib,time,subprocess
P=Path(__file__).resolve().parent;R=P.parents[1];start=time.monotonic()
w=R/'crates/aspis-r1-cost-probe/src/weights.rs';c=R/'crates/aspis-core/src/r0/opening.rs'
def table(s,n):
 return [int(x) for x in re.search(n+r'[^=]*=\s*\[([^]]*)\]',s,re.S)[1].replace('\n','').split(',') if x.strip()]
g=table(w.read_text(),'S2_INACTIVE_GROUPS');m=table(w.read_text(),'S2_INACTIVE_MASKS');a=table(c.read_text(),'COPY_ACTIVE_ROW_MASKS')
bad=[]
for j in range(64):
 for s in range(16):
  r=64*(s%4)+256*(s//4)+(j%4)*16+(j//4%4)+4*(j//16)
  if bool(m[g[j]]&(1<<s)) != (((a[r//16]>>(r%16))&1)==0):bad.append([j,s,r])
x=dict(kind='tiny static integer preflight only',checked_cells=1024,mismatches=bad,wall_seconds=time.monotonic()-start,source_revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),sources={str(p.relative_to(R)):dict(sha256=hashlib.sha256(p.read_bytes()).hexdigest(),bytes=p.stat().st_size) for p in [w,c]},claim='No native Lean row_loop, model inactive-row, Pair or deployed-premise closure is established by this audit.')
(P/'FJc_table_preflight.json').write_text(json.dumps(x,indent=2)+'\n')
print(json.dumps(x,indent=2))
