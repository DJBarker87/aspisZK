"""Replace only an Aeneas literal's default native proof with kernel decide."""
from pathlib import Path
import hashlib,json
E=Path(__file__).resolve().parent
p=E/'NFG_row_extracted/NFG_InverseRef/Funs.lean'
s=p.read_text();old='(toStr "cannot invert zero in QM31")';new='(toStr "cannot invert zero in QM31" (by decide))'
assert s.count(old)==1
before=hashlib.sha256(s.encode()).hexdigest();s=s.replace(old,new);p.write_text(s)
(E/'NFG_LITERAL_NORMALIZATION.json').write_text(json.dumps(dict(path=str(p.relative_to(E)),before=before,after=hashlib.sha256(s.encode()).hexdigest(),replacement=[old,new],reason='L028 exposed generated default native-decide axiom; excluded until kernel proof normalization and focused replay',semantic_change='none: same panic-message UTF-8 bytes; proof witness only'),indent=2)+'\n')
d=json.loads((E/'NFG_GENERATED.json').read_text());d['NFG_InverseRef.Funs']['sha256']=hashlib.sha256(s.encode()).hexdigest();(E/'NFG_GENERATED.json').write_text(json.dumps(d,indent=2)+'\n')
