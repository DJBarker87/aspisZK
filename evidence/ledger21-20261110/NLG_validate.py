from pathlib import Path
import json,lzma,hashlib,subprocess,collections
E=Path(__file__).resolve().parent;H=lambda b:hashlib.sha256(b).hexdigest();J=lambda p:json.loads(lzma.decompress(p.read_bytes())if p.suffix=='.xz'else p.read_bytes())
required=['NLG_LEDGER.json.xz','NLG_LEDGER.json.sha256','NLG_LEDGER_DELTA.json','NLG_PHYSICAL.md','NLG_PLAN_STATUS.md','NLG_COMBINED_IMPORT.lean','NLG_AUDIT.json','NLG_SCAN.json','NLG_HANDOFF.md','NLG_REMAINING.md','NLG_ATTEMPTS.jsonl']
assert all((E/n).is_file()for n in required)
b=J(E.parent/'ledger20-20261109/NKW_LEDGER.json.xz');x=J(E/'NLG_LEDGER.json.xz');by={r['row']:r for r in b['rows']};assert len(x['rows'])==len(by)==599
assert x['trust_rows']==b['trust_rows']and x['counts']=={'CLOSED':564,'OPEN':35}
assert H(lzma.decompress((E/'NLG_LEDGER.json.xz').read_bytes()))==(E/'NLG_LEDGER.json.sha256').read_text().strip()
d=J(E/'NLG_LEDGER_DELTA.json');changed=[]
for r in x['rows']:
 old=by[r['row']];assert r['function']==old['function']and r['canonical_callees']==old['canonical_callees']and r['frozen_body_sha256']==old['frozen_body_sha256']
 clauses=old['obligation']['caller_domain_obligations'];assert r['obligation']['caller_domain_obligations'][:len(clauses)]==clauses
 for k in ['named_hypotheses','inventory_domain_obligations']:assert r['obligation'][k]==old['obligation'][k]
 if r['status']!=old['status']:changed.append(r['row'])
assert set(changed)==set(d['new_closed_rows'])and len(changed)==4
assert d['rejected_candidates']==[]
ks=J(E/'NLG_KERNEL_STATEMENTS.json.xz');owned=0
for r in x['rows']:
 for ro in r['root_owners']:
  s=ks[ro['root']];assert ro['owner_module']==s['owner_module'];owned+=1
scan=J(E/'NLG_SCAN.json');assert scan['exit_status']==scan['dangling']==scan['incompatible_owners']==scan['canonical_duplicate_owners']==scan['import_mismatches']==0
a=J(E/'NLG_AUDIT.json');assert a['full_composition_pass']and a['required_roots']==10720 and a['raw_standard_axioms_only']and len(a['fixtures'])==8
assert a['resources']['scopes']==40 and a['resources']['kani']==a['resources']['extraction']==a['resources']['swaps']==0
sha_pairs=0
for p in E.rglob('*.xz'):
 side=Path(str(p)[:-3]+'.sha256')
 if side.exists():assert H(lzma.decompress(p.read_bytes()))==side.read_text().strip();sha_pairs+=1
oversize=[str(p)for p in E.rglob('*')if p.is_file()and p.stat().st_size>20_000_000];assert not oversize
for p in E.rglob('*'):
 if p.is_file():assert p.suffix not in ['.olean','.ir','.o','.elf','.pyc'],str(p)
assert subprocess.check_output(['git','diff','--name-only','HEAD','--','crates','programs','Cargo.lock'],text=True)==''
source_snapshots=0
for p in E.glob('NLG_L*/receipt.json'):
 r=J(p)
 for name,digest in r['source_hashes'].items():
  q=p.parent/'sources'/name
  if not q.exists():q=Path(str(q)+'.xz');assert q.exists();data=lzma.decompress(q.read_bytes())
  else:data=q.read_bytes()
  assert H(data)==digest,(str(p),name);source_snapshots+=1
assert x['pins']['pool_elf']=='e0e49c344d35575116c0359450315ea4334bfb03006551727f67c04a8cfe09dc'
assert len(J(E/'NLG_PARENT_CLAUSES.json')['native_input_ancestors'])==6
assert J(E/'NLG_SOURCE_OBJECT_REVIEW.json')['status']=='PASS_COMMITTED_SOURCE_HASHES_MATCH_SUCCESSFUL_COMPILES'
out=dict(status='PASS',ledger_rows=599,new_closed=4,rejected_open=0,root_owner_references=owned,source_snapshots=source_snapshots,compressed_sha_pairs=sha_pairs,oversized_files=oversize,shipped_changes=[],runtime_crypto_trust_changed=False,security_target_established=False)
(E/'NLG_VALIDATION.json').write_text(json.dumps(out,indent=1)+'\n');print(json.dumps(out))
