"""One authorized sequence; reviewed callers unmodified; terminal on every error."""
import hashlib,json,os,platform,subprocess,sys,time,traceback,resource
from pathlib import Path
HERE=Path(__file__).resolve().parent
sys.path.insert(0,str(HERE))
import ResourceMeta1G_local as local
OUT=local.OUT
seal=json.loads((OUT/'LIVE-identity-seal.json').read_text())
for name,pin in seal['operational'].items():
    b=(HERE/name).read_bytes()
    assert dict(sha256=hashlib.sha256(b).hexdigest(),size=len(b))==pin
start=time.monotonic();stages=[];code=1;error=None
try:
    for name in ('inspect','stage','preflight','run'):
        begun=time.monotonic()
        item=dict(action=name,started=True)
        stages.append(item)
        result=getattr(local,name)()
        item.update(exit=result or 0,wall_seconds=time.monotonic()-begun)
        if result:
            code=result
            break
    else:code=0
except BaseException as exc:
    error=repr(exc)
    stages[-1].update(exit='exception',error=error,wall_seconds=time.monotonic()-begun)
    traceback.print_exc()
finally:
    u=resource.getrusage(resource.RUSAGE_SELF)
    receipt=dict(command=[sys.executable,'-B',str(Path(__file__).resolve())],source_revision=local.revision(),stages=stages,exit=code,error=error,wall_seconds=time.monotonic()-start,peak_rss_bytes=u.ru_maxrss*(1 if platform.system()=='Darwin' else 1024),swap=u.ru_nswap,metrics_scope='local sequence driver only; transport/helper/original run separate',sampled_aggregate_peak='unknown/unmeasured locally',print_axioms='N/A',host_sequence='one inspect -> stage -> preflight -> run; no retry; export separate existing-capture authority')
    local.save('LIVE-sequence-receipt.json',receipt)
    print(json.dumps(receipt),flush=True)
sys.exit(code)
