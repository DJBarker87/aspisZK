"""Fresh local source-only reproduction of the prospective package, no execution."""
import hashlib
import json
from pathlib import Path
import resource
import sys
import time

E=Path(__file__).resolve().parent
D=E.parents[5]/'tools/prover-rw-20261023/final-native-gate'
OUT=Path('/private/tmp/FinalNativeGate-data-reproduction-20261025-v1')

def pin(raw):return dict(size=len(raw),sha256=hashlib.sha256(raw).hexdigest())

def main():
    start=time.monotonic();source=D/'FinalNativeGate-data-release-build.py'
    ns={'__name__':'source_preparation_only','__file__':str(source)}
    exec(source.read_bytes(),ns);ns['RELEASE']=OUT
    report=ns['prepare']()
    actual={str(p.relative_to(OUT)):pin(p.read_bytes()) for p in sorted(OUT.rglob('*')) if p.is_file()}
    expected={str(p.relative_to(D/'prospective-data-v3')):pin(p.read_bytes()) for p in sorted((D/'prospective-data-v3').rglob('*')) if p.is_file()}
    assert actual==expected
    usage=resource.getrusage(resource.RUSAGE_SELF)
    receipt=dict(argv=[sys.executable,'-B',str(Path(__file__))],exit=0,wall_seconds=time.monotonic()-start,
        peak_rss_bytes=usage.ru_maxrss*(1 if sys.platform=='darwin' else 1024),swap=usage.ru_nswap,
        source_revision='75c38375fee5f48995d24101d235f1ec5aca8f36 plus exact source-manifest-008 overlay',
        harness=pin(Path(__file__).read_bytes()),builder=pin(source.read_bytes()),
        source_dependency_manifest=pin((E/'FinalNativeGate-source-manifest-008.json').read_bytes()),
        prepared_artifacts=actual,source_preparation_directory=str(OUT),receiver=report['receiver'],
        print_axioms='N/A: finite source preparation and hashes; no formal theorem or tool invocation',
        actual_host=0,actual_SSH=0,actual_network=0,actual_metadata=0,actual_setup=0,actual_native=0,actual_compiler=0,
        actual_Rust=0,actual_Cargo=0,actual_Kani=0,actual_Lean=0,actual_extraction=0,actual_backend=0,actual_ELF=0)
    with (E/'FinalNativeGate-prepare-reproduce-008.json').open('x') as f:json.dump(receipt,f,sort_keys=True,indent=2)
    print(json.dumps({k:receipt[k] for k in ('exit','wall_seconds','peak_rss_bytes','swap','receiver')}))

if __name__=='__main__':main()
