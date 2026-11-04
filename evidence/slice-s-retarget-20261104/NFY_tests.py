"""Mutation checks for coherence and additive row-admission gates; no prover."""
from pathlib import Path
import sys,json,lzma,copy
sys.dont_write_bytecode=True
from NFY_checks import check_bundle,check_delta
E=Path(__file__).resolve().parent;J=lambda p:json.loads(p.read_text())
a=J(E/'NFY_AUDIT.json');s=[json.loads(l) for l in (E/'NFY_LOADED_scan.jsonl').read_text().splitlines()];m=J(E/'NFY_AUDIT_ROOTS.json');d=J(E/'NFY_LEDGER_DELTA.json');g=J(E/'NFY_CERTIFICATE_GAPS.json');c=J(E/'NFY_CERTIFICATES.json');b=json.loads(lzma.decompress((E.parent/'ledger7-20261104/NFX_LEDGER.json.xz').read_bytes()))
assert check_bundle(a,s,m) and check_delta(b,d,g,c,s)
checks=[]
def reject(name,fn):
 try:fn()
 except (AssertionError,KeyError,ValueError,TypeError):checks.append(name);return
 raise AssertionError('mutation accepted: '+name)
def bundle(name,edit):
 aa=copy.deepcopy(a);ss=copy.deepcopy(s);mm=copy.deepcopy(m);edit(aa,ss,mm);reject(name,lambda:check_bundle(aa,ss,mm))
def delta(name,edit):
 dd=copy.deepcopy(d);gg=copy.deepcopy(g);cc=copy.deepcopy(c);edit(dd,gg,cc);reject(name,lambda:check_delta(b,dd,gg,cc,s))
bundle('wrong headline',lambda a,s,m:a.update(headline='AspisR1.Other.deployed'))
bundle('dropped raw root',lambda a,s,m:a['results'].pop())
bundle('duplicated raw root',lambda a,s,m:a['results'].append(copy.deepcopy(a['results'][0])))
bundle('nonstandard raw axiom',lambda a,s,m:a['results'][0]['walked_axioms'].append('badAxiom'))
bundle('nonstandard summary axiom',lambda a,s,m:a['results'][0]['collect_axioms'].append('badAxiom'))
bundle('unrelated root list',lambda a,s,m:m['roots'].append('Missing.root'))
bundle('missing parent scope',lambda a,s,m:a['results'][0].update(parent_attempt=''))
bundle('fixture axiom hidden',lambda a,s,m:a['fixtures'][0].update(walked_axioms=[]))
bundle('mutation reports planted axiom',lambda a,s,m:a['fixtures'][4].update(walked_axioms=['badAxiom']))
bundle('fixture collect mismatch',lambda a,s,m:a['fixtures'][0].update(equal=False))
bundle('dangling declaration',lambda a,s,m:s[0]['dangling'].append(dict(missing='bad')))
bundle('incompatible owner',lambda a,s,m:s[0]['duplicate_owners'].append(dict(name='bad')))
bundle('import mismatch',lambda a,s,m:s[0].update(imports_match=False))
bundle('legacy Prepared reintroduced',lambda a,s,m:s.append(dict(module='PreparedFromQmSourceBridge',dangling=[],duplicate_owners=[],imports_match=True)))
bundle('walker changed',lambda a,s,m:a['walker_conformance'].update(byte_identical=False))
delta('drop a required auxiliary reference',lambda d,g,c:g.pop())
def unsupported(d,g,c):
 r=copy.deepcopy(d['promotions'][0]);r.update(row=d['remaining_qualified_S'][0]['row']);d['promotions'].append(r)
delta('unsupported promotion',unsupported)
delta('missing admitted promotion',lambda d,g,c:d['promotions'].pop())
delta('wrong frozen function',lambda d,g,c:d['promotions'][0].update(function='wrong'))
delta('wrong frozen body',lambda d,g,c:d['promotions'][0].update(frozen_body_sha256='0'*64))
delta('new trust smuggled',lambda d,g,c:d['new_trust_rows'].append('badTrust'))
delta('old trust silently removed',lambda d,g,c:d['removed_trust_rows'].append('RuntimePersistence'))
delta('cold release overstated',lambda d,g,c:d.update(cold_release_replay=True))
delta('security target overstated',lambda d,g,c:d.update(security_target_established=True))
delta('forged count',lambda d,g,c:d['after'].update(CLOSED=256))
result=dict(positive=True,rejected_mutations=len(checks),checks=checks,scope='Evidence-gate mutation tests only; no Lean/Kani/native proof launches')
(E/'NFY_TESTS.json').write_text(json.dumps(result,indent=1)+'\n');print(json.dumps(result))
