"""Focused mutation tests for new additive evidence gates; no prover replay."""
from pathlib import Path
import json,lzma,copy,sys
sys.dont_write_bytecode=True
from NGE_checks import check_bundle,check_delta
E=Path(__file__).resolve().parent;J=lambda p:json.loads(p.read_text())
a=J(E/'NGE_AUDIT.json');s=[json.loads(l) for l in (E/'NGE_LOADED_scan.jsonl').read_text().splitlines()];m=J(E/'NGE_AUDIT_ROOTS.json');c=J(E/'NGE_CERTIFICATES.json');p=J(E/'NGE_PROVENANCE.json');d=J(E/'NGE_LEDGER_DELTA.json');prior=J(E.parent/'slice-s-retarget-20261104/NFY_LEDGER_DELTA.json');base=json.loads(lzma.decompress((E.parent/'ledger7-20261104/NFX_LEDGER.json.xz').read_bytes()))
results=[]
def rejects(name,f):
 try:f()
 except (AssertionError,KeyError):results.append(dict(test=name,rejected=True));return
 raise AssertionError('mutation accepted: '+name)
assert check_bundle(a,s,m,c,p) and check_delta(base,prior,d,c,s)
x=copy.deepcopy(a);x['results'][0]['walked_axioms'].append('NGE_Planted.bad');rejects('nonstandard raw axiom',lambda:check_bundle(x,s,m,c,p))
x=copy.deepcopy(a);x['results']=x['results'][1:];rejects('missing raw root',lambda:check_bundle(x,s,m,c,p))
x=copy.deepcopy(s);x[0]['dangling']=['NGE_Planted.missing'];rejects('dangling reference',lambda:check_bundle(a,x,m,c,p))
x=copy.deepcopy(s);x[0]['duplicate_owners']=['NGE_Planted.owner'];rejects('incompatible owner',lambda:check_bundle(a,x,m,c,p))
x=copy.deepcopy(s);x[0]['imports_match']=False;rejects('import mismatch',lambda:check_bundle(a,x,m,c,p))
x=copy.deepcopy(a);x['proof_driver_binary_sha256'].append('wrong');rejects('different fixture binary',lambda:check_bundle(x,s,m,c,p))
x=copy.deepcopy(d);x['promotions']=x['promotions'][1:];rejects('missing promotion',lambda:check_delta(base,prior,x,c,s))
x=copy.deepcopy(d);x['remaining_qualified_S']=[];rejects('hidden remaining obligation',lambda:check_delta(base,prior,x,c,s))
x=copy.deepcopy(d);x['new_trust_rows']=['unapproved'];rejects('added trust',lambda:check_delta(base,prior,x,c,s))
x=copy.deepcopy(c);next(t for row in x['rows'] for t in row['theorems'] if t['canonical_module'].startswith('NGE_'))['canonical_name']='NGE_Planted.unloaded';rejects('selected theorem absent from raw audit',lambda:check_bundle(a,s,m,x,p))
x=copy.deepcopy(s);x=[r for r in x if r['module']!='NGE_NEQ_ParserCanonical'];rejects('loaded certificate module omitted',lambda:check_delta(base,prior,d,c,x))
(E/'NGE_TESTS.json').write_text(json.dumps(dict(status='PASS',positive_bundle=True,positive_delta=True,mutations=results),indent=1)+'\n');print(json.dumps(dict(status='PASS',mutations=len(results))))
