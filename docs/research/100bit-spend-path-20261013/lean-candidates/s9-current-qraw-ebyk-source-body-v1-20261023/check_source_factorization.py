from pathlib import Path
import hashlib,json,sys
root=Path(__file__).resolve().parent
assert len(sys.argv)==2, 'usage: check_source_factorization.py PINNED_PRODUCTION_PAIR_FUNS.lean'
src=Path(sys.argv[1]).read_text()
out=(root/'sources/S9ActualRawEbyKBodyV1.lean').read_text();pins=json.loads((root/'source-body-pins.json').read_text())
assert hashlib.sha256(src.encode()).hexdigest()==pins['source_funs_sha256']
for name,new,key in [('fast_pairing.canonical.Dot.push','dotWithRaw','dot_push_original_sha256'),('fast_pairing.EbyKDot.push','pushWithRaw','ebyk_push_original_sha256')]:
 st=src.index('def '+name+'\n');en=src.index('\n/--',st);original=src[st:en]
 assert hashlib.sha256(original.encode()).hexdigest()==pins[key]
 expected=original.replace('def '+name,'def '+new+' (raw : A4 → A4 → Result R4)')
 if new=='dotWithRaw':expected=expected.replace('fast_pairing.canonical.Q.raw a b','raw a b')
 else:
  expected=expected.replace('fast_pairing.canonical.Dot.push self.c0','dotWithRaw raw self.c0').replace('fast_pairing.canonical.Dot.push self.c1','dotWithRaw raw self.c1')
 assert expected in out
print('PASS: both exact original source bodies differ only by explicit raw callee parameterization')
