"""Read-only replay of adopted z(1) certificate and original 17 controls."""
from pathlib import Path
import sys,json,hashlib,time
sys.dont_write_bytecode=True
E=Path(__file__).resolve().parent;P=E.parent/'slice-q-fnptr-20261029'
sys.path.insert(0,str(P));import NEF_OBSERVER_CERTIFICATE as cert

def review():
 src,nodes=cert.inputs();result=cert.validate(src,nodes)
 old=(P/'NEF_OBSERVER_TESTS.py').read_text()
 marker="(E/'NEF_OBSERVER_TEST_RESULTS.json')";assert old.count(marker)==1
 changed=old.replace(marker,"(Path("+repr(str(E))+ ")/'NEO_OBSERVER_TESTS.json')")
 assert changed.replace("(Path("+repr(str(E))+ ")/'NEO_OBSERVER_TESTS.json')",marker)==old
 exec(compile(changed,str(P/'NEF_OBSERVER_TESTS.py'),'exec'),dict(__name__='NEO_observer_controls'))
 tests=json.loads((E/'NEO_OBSERVER_TESTS.json').read_text());assert tests['positive'] and len(tests['mutation_tests'])==17
 return dict(frozen_revision=cert.REV,certificate=result,source_hashes={n:hashlib.sha256(s.encode()).hexdigest() for n,s in src.items()},scripts={n:hashlib.sha256((P/n).read_bytes()).hexdigest() for n in ['NEF_OBSERVER_CERTIFICATE.py','NEF_OBSERVER_TESTS.py']},adoption='C3-BIN 2026-11-02 ruling z(1)',historical_native_credit_restored=[],native_pointer_property=False,print_axioms='NEO_L001: mark/continuation/frame, standard axioms only',controls=17)
if __name__=='__main__':
 result=review();(E/'NEO_OBSERVER_REVIEW.json').write_text(json.dumps(result,indent=1)+'\n')
