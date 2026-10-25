"""Local offline Python-only receipt runner; 512 MiB measured peak ceiling."""
import hashlib
import json
import resource
import subprocess
import sys
import time
from pathlib import Path

ROOT=Path(__file__).resolve().parents[2]
HERE=Path(__file__).resolve().parent
OUT=ROOT/'evidence/resource-rss-go-20261025'


def pin(raw):return dict(sha256=hashlib.sha256(raw).hexdigest(),size=len(raw))


def main():
    target,label=sys.argv[1:]
    assert Path(target).name==target and target.startswith('ResourceRssGO_') and target.endswith('.py')
    assert label.replace('-','').isalnum()
    command=[sys.executable,'-B',str(HERE/target)]
    sources={p.name:pin(p.read_bytes()) for p in sorted(HERE.glob('*.py'))}
    revision=subprocess.check_output(['git','rev-parse','HEAD'],cwd=ROOT,text=True).strip()
    start=time.monotonic()
    with (OUT/(label+'.log')).open('xb') as stream:
        done=subprocess.run(command,cwd=HERE,stdout=stream,stderr=subprocess.STDOUT)
    elapsed=time.monotonic()-start
    usage=resource.getrusage(resource.RUSAGE_CHILDREN)
    # Isolated runner's preceding git call is tiny. RUSAGE_CHILDREN peak is the
    # maximum child RSS, not sum; no previous test child exists in this runner.
    rss=usage.ru_maxrss if sys.platform=='darwin' else usage.ru_maxrss*1024
    receipt=dict(command=command,target=target,exit=done.returncode,wall_seconds=elapsed,
        peak_rss_bytes=rss,swap=usage.ru_nswap,memory_ceiling_bytes=512*2**20, ceiling_kind='post-run measured RSS; Darwin rejects RLIMIT_AS/DATA lowering',
        source_revision=revision,sources=sources,interpreter=dict(path=sys.executable,
            version=sys.version,**pin(Path(sys.executable).read_bytes())),
        output=pin((OUT/(label+'.log')).read_bytes()),print_axioms='N/A; no Lean or formal execution')
    with (OUT/(label+'-receipt.json')).open('x') as f:f.write(json.dumps(receipt,sort_keys=True,indent=2)+'\n')
    print(json.dumps({k:receipt[k] for k in ('target','exit','wall_seconds','peak_rss_bytes','swap')},sort_keys=True))
    assert rss < 512*2**20, 'local Python memory ceiling crossed; do not rerun unchanged'
    raise SystemExit(done.returncode)


if __name__=='__main__':main()
