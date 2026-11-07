"""Final independent artifact/receipt validation; no theorem rerun."""
from pathlib import Path
import json,lzma,hashlib,subprocess,collections
E=Path(__file__).resolve().parent;H=lambda b:hashlib.sha256(b).hexdigest()
def raw(p):
 if p.exists():return p.read_bytes()
 b=lzma.decompress(Path(str(p)+'.xz').read_bytes());assert H(b)==Path(str(p)+'.sha256').read_text().strip();return b
def J(p):return json.loads(lzma.decompress(raw(p))if p.suffix=='.xz'else raw(p))
assert not(E/'NNK_CLIENT_ACTIVE').exists()
assert len(list(E.glob('NNK_L*/receipt.json')))==60
pairs=0;snapshots=0
for p in E.rglob('*.xz'):
 b=lzma.decompress(p.read_bytes());q=Path(str(p)[:-3]+'.sha256');assert q.exists()and H(b)==q.read_text().strip(),str(p);pairs+=1
for p in E.glob('NNK_L*/receipt.json'):
 r=J(p);ad=J(E/(r['attempt']+'-admission.json'));assert ad['exit']==0 and ad['reservation']['allowed']is True
 assert r['limits']=={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'}and str(r['swaps'])=='0'
 for name,digest in r['source_hashes'].items():assert H(raw(p.parent/'sources'/name))==digest;snapshots+=1
ledger=J(E/'NNK_LEDGER.json.xz');basis=J(E.parent/'ledger26-20261111/NNI_LEDGER.json.xz');before={r['row']:r for r in basis['rows']};by={r['row']:r for r in ledger['rows']};delta=J(E/'NNK_LEDGER_DELTA.json');assert len(by)==len(ledger['rows'])==599
assert dict(collections.Counter(r['status']for r in ledger['rows']))=={'CLOSED':587,'OPEN':12}
assert {r for r in by if by[r]['status']!=before[r]['status']}=={'TX1:137','TX1:087','TX2:217','TX2:234'}
assert all(by[n]['canonical_callees']==r['canonical_callees']for n,r in before.items())
assert by['TX2:233']['status']=='OPEN'and ledger['security_target_established']is False
for c in J(E/'NNK_CANDIDATE_REVIEW.json')['candidates']:assert c['gate_admitted']and c['status']=='PASS_COMPLETE_ROOT_GATE_ADMITTED'and c['remaining_parameters']==[]
assert delta['added_edges']==delta['removed_edges']==delta['trust_inventory_removals']==[]
oldtrust={r['id']:r for r in basis['trust_rows']};newtrust={r['id']:r for r in ledger['trust_rows']};assert set(oldtrust)==set(newtrust)
for n,r in oldtrust.items():
 for key in ['statement','status','removal_condition']:assert r.get(key)==newtrust[n].get(key),(n,key)
assert newtrust['ReviewedTranscription-TX2:217']['direct_closed_rows']==['TX2:217']
for n in ['ReviewedTranscription-TX1:344','ReviewedTranscription-TX2:240']:assert newtrust[n].get('consumed_by_closed_rows',[])==[]
assert J(E/'NNK_AUDIT.json')['full_composition_pass']and J(E/'NNK_SCAN.json')['exit_status']==0
assert J(E/'NNK_OWNER_COMPARISON.json')['identical']==12600
assert set(J(E/'NNK_PROVENANCE.json')['current_conservative_affected_CLOSED_rows'])<={n for n,r in by.items()if r['status']=='CLOSED'}
assert J(E/'NNK_PROVENANCE.json')['historical_verbatim']==J(E.parent/'ledger26-20261111/NNI_PROVENANCE.json')['historical_verbatim']
assert J(E/'NNK_K086.json')==J(E.parent/'ledger26-20261111/NNI_K086.json')
assert J(E/'NNK_RESOURCES.json')['timeout_or_memory_kill']==['NNK_L046']
assert not any(p.stat().st_size>20_000_000 for p in E.rglob('*')if p.is_file())
assert not subprocess.check_output(['git','diff','4bb3b3f51e16b4525f1d10336e2b0bcbbd775387','HEAD','--','crates','programs/r1-cost-probe','Cargo.lock'])
assert not subprocess.check_output(['git','diff','b936275465600469312d1f058cdc91ea2a11f3dc','HEAD','--','programs/aspis-pool'])
assert not subprocess.check_output(['git','diff','--','crates','programs','Cargo.lock'])
for a,n in [(54,'137'),(55,'087'),(56,'234')]:
 r=J(E/f'NNK_L{a:03}/receipt.json');assert r['exit_status']==0
 assert r['print_axioms']and all('sorryAx'not in l for l in r['print_axioms'])
out=dict(status='PASS',compressed_sha_pairs=pairs,source_snapshots=snapshots,receipts=60,rows=599,counts=ledger['counts'],gate='PASS',source_and_trust_statements_unchanged=True,shipped_source_unchanged=True,new_kani=0,new_extraction=0,no_push=True,no_key_actions=True)
(E/'NNK_VALIDATION.json').write_text(json.dumps(out,indent=1)+'\n');print(json.dumps(out))
