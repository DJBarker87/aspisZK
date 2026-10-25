"""One local ordinary Python test suite, measured RSS below512MiB, no host work."""
import contextlib
import hashlib
import json
from pathlib import Path
import resource
import subprocess
import sys
import time
import unittest
import types
import traceback

HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[1]
OUT=ROOT/'evidence/sbf-seal-20261025'


def pin(raw):return dict(sha256=hashlib.sha256(raw).hexdigest(),size=len(raw))


def main():
    label=sys.argv[1]
    assert label.replace('-','').isalnum() and label.startswith('SbfSeal-')
    revision=subprocess.check_output(['git','rev-parse','HEAD'],cwd=ROOT,text=True).strip()
    start=time.monotonic()
    with (OUT/(label+'.log')).open('x') as stream:
        with contextlib.redirect_stdout(stream),contextlib.redirect_stderr(stream):
            try:
                if label.endswith('-review'):
                    import SbfSeal_review
                    SbfSeal_review.main()
                    result=types.SimpleNamespace(testsRun=0,failures=[],errors=[],wasSuccessful=lambda:True)
                elif label.endswith('-audit'):
                    import SbfSeal_audit
                    result=SbfSeal_audit.main()
                else:
                    import SbfSeal_tests
                    suite=unittest.defaultTestLoader.loadTestsFromModule(SbfSeal_tests)
                    result=unittest.TextTestRunner(stream=stream,verbosity=2).run(suite)
            except Exception:
                traceback.print_exc()
                result=types.SimpleNamespace(testsRun=0,failures=[],errors=['runner exception'],wasSuccessful=lambda:False)
    usage=resource.getrusage(resource.RUSAGE_SELF)
    rss=usage.ru_maxrss*(1 if sys.platform=='darwin' else 1024)
    sources={p.name:pin(p.read_bytes()) for p in sorted(HERE.glob('*.py'))}
    dependencies={}
    for mod in list(sys.modules.values()):
        path=getattr(mod,'__file__',None)
        if path and Path(path).is_file():
            dependencies[str(Path(path).absolute())]=pin(Path(path).read_bytes())
    code=0 if result.wasSuccessful() and rss<512*2**20 else 1
    receipt=dict(command=[sys.executable,'-B',str(Path(__file__).absolute()),label],
        target='SbfSeal_tests ordinary paths + explicitly synthetic boundary metadata',
        exit=code,tests=result.testsRun,failures=len(result.failures),errors=len(result.errors),
        wall_seconds=time.monotonic()-start,peak_rss_bytes=rss,swap=usage.ru_nswap,
        source_revision=revision,sources=sources,dependencies=dependencies,
        runtime=dict(executable=sys.executable,version=sys.version,**pin(Path(sys.executable).read_bytes())),
        log=pin((OUT/(label+'.log')).read_bytes()),print_axioms='N/A; no formal execution',
        memory_limit='512MiB post-run measured ceiling; small bounded fixtures, no Linux scope claim',
        zero_operations=['host','network','privilege','namespace','mount','scope','GO','compiler','Cargo','rustc','Lean','Kani','native-probe','ELF','key','RPC'],
        synthetic_claim='No Linux kernel/proc/sudo/current-producer execution or integration validated')
    (OUT/(label+'-receipt.json')).write_text(json.dumps(receipt,sort_keys=True,indent=2)+'\n')
    print(json.dumps({k:receipt[k] for k in ('exit','tests','failures','errors','wall_seconds','peak_rss_bytes','swap')}))
    raise SystemExit(code)


if __name__=='__main__':main()
