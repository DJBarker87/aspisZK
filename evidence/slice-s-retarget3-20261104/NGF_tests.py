"""Mutation tests for independent complete-certificate and coherence admission."""
from pathlib import Path
import sys,json,lzma,copy
sys.dont_write_bytecode=True
from NGF_checks import check_bundle,check_delta
E=Path(__file__).resolve().parent;J=lambda p:json.loads(p.read_text())
a=J(E/'NGF_AUDIT.json');scan=[json.loads(l) for l in (E/'NGF_LOADED_scan.jsonl').read_text().splitlines()];m=J(E/'NGF_AUDIT_ROOTS.json');d=J(E/'NGF_LEDGER_DELTA.json');cert=json.loads(lzma.decompress((E/'NGF_CERT_ASSOCIATIONS.json.xz').read_bytes()));inv=J(E/'NGF_CERT_INVENTORY.json');prov=J(E/'NGF_PROVENANCE.json');base=json.loads(lzma.decompress((E.parent/'ledger7-20261104/NFX_LEDGER.json.xz').read_bytes()));prior=J(E.parent/'slice-s-retarget-20261104/NFY_LEDGER_DELTA.json')
assert check_bundle(a,scan,m) and check_delta(base,prior,d,cert,inv,scan,prov)
checks=[]
def reject(name,fn):
 try:fn()
 except (AssertionError,KeyError,ValueError,TypeError):checks.append(name);return
 raise AssertionError('mutation accepted '+name)
def bundle(name,edit):
 aa=copy.deepcopy(a);ss=copy.deepcopy(scan);mm=copy.deepcopy(m);edit(aa,ss,mm);reject(name,lambda:check_bundle(aa,ss,mm))
def delta(name,edit):
 dd=copy.deepcopy(d);cc=copy.deepcopy(cert);edit(dd,cc);reject(name,lambda:check_delta(base,prior,dd,cc,inv,scan,prov))
bundle('wrong headline',lambda a,s,m:a.update(headline='Wrong.deployed'))
bundle('dropped raw root',lambda a,s,m:a['results'].pop())
bundle('duplicate raw root',lambda a,s,m:a['results'].append(a['results'][0]))
bundle('nonstandard raw axiom',lambda a,s,m:a['results'][0]['walked_axioms'].append('badAxiom'))
bundle('nonstandard summary axiom',lambda a,s,m:a['results'][0]['collect_axioms'].append('badAxiom'))
bundle('missing parent receipt',lambda a,s,m:a['results'][0].update(parent_attempt=''))
bundle('fixture axiom hidden',lambda a,s,m:a['fixtures'][0].update(walked_axioms=[]))
bundle('mutation reports planted axiom',lambda a,s,m:a['fixtures'][4].update(walked_axioms=['badAxiom']))
bundle('fixture summary mismatch',lambda a,s,m:a['fixtures'][0].update(equal=False))
bundle('dangling reference',lambda a,s,m:s[0]['dangling'].append(dict(missing='bad')))
bundle('incompatible owner',lambda a,s,m:s[0]['duplicate_owners'].append(dict(name='bad')))
bundle('import mismatch',lambda a,s,m:s[0].update(imports_match=False))
bundle('legacy owner imported',lambda a,s,m:s.append(dict(module='PreparedFromQmSourceBridge',dangling=[],duplicate_owners=[],imports_match=True)))
bundle('walker changed',lambda a,s,m:a['walker_conformance'].update(byte_identical=False))
delta('missing auxiliary gap',lambda d,c:c['gaps'].pop())
delta('dropped theorem occurrence',lambda d,c:c['rows'][0]['theorems'].pop())
delta('changed certificate statement',lambda d,c:c['rows'][0]['theorems'][0].update(statement_after='True'))
delta('changed certificate name',lambda d,c:c['rows'][0]['theorems'][0].update(canonical_name='Wrong.name'))
delta('missing admitted promotion',lambda d,c:d['promotions'].pop())
def unsupported(d,c):
 r=copy.deepcopy(d['promotions'][0]);r['row']=d['remaining_qualified_S'][0]['row'];d['promotions'].append(r)
delta('unsupported promotion',unsupported)
delta('wrong frozen function',lambda d,c:d['promotions'][0].update(function='wrong'))
delta('wrong frozen body',lambda d,c:d['promotions'][0].update(frozen_body_sha256='0'*64))
delta('new trust smuggled',lambda d,c:d['new_trust_rows'].append('badTrust'))
delta('trust removed',lambda d,c:d['removed_trust_rows'].append('RuntimePersistence'))
delta('cold replay overstated',lambda d,c:d.update(cold_release_replay=True))
delta('security target overstated',lambda d,c:d.update(security_target_established=True))
delta('wrong inventory basis',lambda d,c:d.update(inventory_rows=587))
delta('forged count',lambda d,c:d['after'].update(CLOSED=599))
out=dict(positive=True,rejected_mutations=len(checks),checks=checks,scope='Evidence admission tests, no prover launch')
(E/'NGF_TESTS.json').write_text(json.dumps(out,indent=1)+'\n');print(json.dumps(out))
