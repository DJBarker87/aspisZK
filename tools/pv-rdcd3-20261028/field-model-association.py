"""Supporting Lean program-body identity, never a native checker or b3p6-1 claim.
Rust association remains the complete own-1 source binding; types stay separate.
"""
from pathlib import Path
import re,json,hashlib
D=Path('/home/dombarker/project-offloads/codex-pv-rdcd3-20261028');L=D/'lean-sources/R1Z'
def sha(b):return hashlib.sha256(b).hexdigest()
def definitions(p):
 text=re.sub(r'/\-.*?\-/','',p.read_text(),flags=re.S);out={}
 for m in re.finditer(r'^def\s+(aspis_core\.field\.[\w.]+)',text,re.M):
  rest=text[m.start():];end=re.search(r'\n(?:@\[|def\b|abbrev\b|structure\b|namespace\b|end\b|#)',rest)
  body=rest[:end.start()] if end else rest
  # Keep string contents, ignoring whitespace only outside strings.
  normalized=re.sub(r'("(?:\\.|[^"\\])*")|\s+',lambda m:m[1] or '',body)
  out[m[1]]=sha(normalized.encode())
 return out
p=L/'PV_RDCD3_FieldSource.lean';base=definitions(p);records=[]
for name,count in [('PV_B2_C_RawWeights253Funs',21),('PV_B2_C_RawWeights251Funs',22),('PV_AL_CircleOwnedFuns',25)]:
 q=L/(name+'.lean');other=definitions(q);common=sorted(set(base)&set(other));assert len(common)==count
 assert all(base[k]==other[k] for k in common),(name,[k for k in common if base[k]!=other[k]])
 records.append(dict(module=name,source_sha256=sha(q.read_bytes()),definitions={k:base[k] for k in common}))
j=dict(reference_model_sha256=sha(p.read_bytes()),records=records,scope='Common Lean straight-line field bodies only. Separate carriers remain separate; no inter-carrier theorem or whole native cone follows from counts. Row-specific control/loop/inverse laws and source bindings remain required.',classification='Supporting owned-model text identity only; not a native source checker, not an extractor-generation receipt, and not the b3p6-1 token-identity route. Native associations remain reclassification within existing compiler/Aeneas trust under own-1/k-prime, never premise removal.')
(D/'field-model-association-result.json').write_text(json.dumps(j,indent=2)+'\n');print('Common Lean field programs match:21/22/25 definitions; supporting evidence only')
