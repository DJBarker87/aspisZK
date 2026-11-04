"""Execute unchanged NFX builder, compare historical baseline, add no credit."""
from pathlib import Path
import sys,json,lzma,hashlib,time,resource,subprocess,traceback
sys.dont_write_bytecode=True
E=Path(__file__).resolve().parent;R=E.parents[1]
for d in (R/'evidence').iterdir():
 if d.is_dir():sys.path.insert(0,str(d))
start=time.monotonic();rc=0
try:
 import NFX_ledger as inherited
 d,r,t=inherited.build();baseline=json.loads(lzma.decompress((inherited.E/'NFX_LEDGER.json.xz').read_bytes()))
 d['NFX_source_revision']=baseline['NFX_source_revision']
 assert d==baseline,'unchanged NFX builder disagrees with committed baseline'
 result=dict(coverage=d['NFX_coverage'],same_inventory=True,unchanged_builder=True)
except Exception:rc=1;result=dict(error=traceback.format_exc());traceback.print_exc()
u=resource.getrusage(resource.RUSAGE_SELF)
receipt=dict(attempt='NFY_REPLAY_NFX_LEDGER',exit_status=rc,wall_seconds=time.monotonic()-start,peak_rss_bytes=u.ru_maxrss,swaps=u.ru_nswap,source_revision=subprocess.check_output(['git','rev-parse','HEAD'],cwd=R,text=True).strip(),target='unchanged NFX_ledger.build plus exact baseline equality (only reporting revision normalized)',print_axioms='N/A Python; no prover launch',result=result)
(E/'NFY_REPLAY_NFX_LEDGER.json').write_text(json.dumps(receipt,indent=1)+'\n')
with (E/'NFY_ATTEMPTS.jsonl').open('a') as f:f.write(json.dumps(receipt)+'\n')
print(json.dumps(receipt));sys.exit(rc)
