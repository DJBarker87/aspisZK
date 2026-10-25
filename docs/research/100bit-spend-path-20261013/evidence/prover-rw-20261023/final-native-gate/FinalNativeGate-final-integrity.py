"""Final finite source/hash audit only. No operational launch or test replay."""
import hashlib
import json
from pathlib import Path
import resource
import sys
import time

E=Path(__file__).resolve().parent
D=E.parents[5]/'tools/prover-rw-20261023/final-native-gate'

def pin(raw):return dict(size=len(raw),sha256=hashlib.sha256(raw).hexdigest())

def main():
    start=time.monotonic()
    manifest=json.loads((E/'FinalNativeGate-source-manifest-008.json').read_bytes())
    actual={str(p.relative_to(D)):pin(p.read_bytes()) for p in sorted(D.rglob('*')) if p.is_file()}
    assert actual==manifest
    release=D/'prospective-data-v3'
    identities=json.loads((release/'FinalNativeGate-release-identities.json').read_bytes())
    for name,row in identities['source_manifest'].items():assert pin((D/name).read_bytes())==row
    assert pin((release/'FinalNativeGate-data-transfer.py').read_bytes())==identities['receiver']
    assert pin((release/'FinalNativeGate-data-transport.py').read_bytes())==identities['transport']
    # All retained/prospective data fit the repository's derived JSON policy.
    for base in (D,E):
        for p in base.rglob('*'):
            if p.is_file():
                assert p.suffix not in ('.pyc','.o','.olean','.elf','.rlib','.rmeta')
                if p.suffix=='.json':assert p.stat().st_size<=5_000_000
    usage=resource.getrusage(resource.RUSAGE_SELF)
    result=dict(argv=[sys.executable,'-B',str(Path(__file__))],exit=0,wall_seconds=time.monotonic()-start,
        peak_rss_bytes=usage.ru_maxrss*(1 if sys.platform=='darwin' else 1024),swap=usage.ru_nswap,
        source_revision='75c38375fee5f48995d24101d235f1ec5aca8f36 plus exact source-manifest-008 overlay',
        harness=pin(Path(__file__).read_bytes()),source_dependency_manifest=pin((E/'FinalNativeGate-source-manifest-008.json').read_bytes()),
        receiver=identities['receiver'],transport=identities['transport'],
        handoff=pin((E/'FinalNativeGate-ORDER-RELEASE-HANDOFF.md').read_bytes()),
        print_axioms='N/A: finite source/derived data hashes; no formal theorem/import invocation',
        actual_host=0,actual_SSH=0,actual_network=0,actual_metadata=0,actual_setup=0,actual_native=0,actual_compiler=0,
        actual_Rust=0,actual_Cargo=0,actual_Kani=0,actual_Lean=0,actual_extraction=0,actual_backend=0,actual_ELF=0,
        security_targets_established=False,stop='Lead source/release review and explicit new allocation required')
    with (E/'FinalNativeGate-final-integrity-008.json').open('x') as f:json.dump(result,f,sort_keys=True,indent=2)
    print(json.dumps(result,sort_keys=True))

if __name__=='__main__':main()
