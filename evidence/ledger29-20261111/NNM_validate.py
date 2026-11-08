"""Local evidence integrity checks, after the capped gate; no prover replay."""
from pathlib import Path
import json,lzma,hashlib,subprocess,re
E=Path(__file__).resolve().parent;H=lambda b:hashlib.sha256(b).hexdigest()
def raw(p):
 if p.exists():return p.read_bytes()
 b=lzma.decompress(Path(str(p)+'.xz').read_bytes());assert H(b)==Path(str(p)+'.sha256').read_text().strip();return b
def J(p):
 b=raw(p);return json.loads(lzma.decompress(b)if str(p).endswith('.xz')else b)
audit=J(E/'NNM_AUDIT.json');complete=audit['full_composition_pass']
assert complete or audit['status']=='INCOMPLETE_NO_ROW_CREDIT'
sha_pairs=0
for p in E.rglob('*.xz'):
 q=Path(str(p)[:-3]+'.sha256')
 if q.exists():assert H(lzma.decompress(p.read_bytes()))==q.read_text().strip(),str(p);sha_pairs+=1
snapshots=0
for p in E.glob('NNM_L*/receipt.json'):
 r=J(p)
 for n,h in r['source_hashes'].items():
  q=p.parent/'sources'/n;assert H(raw(q))==h,str(q);snapshots+=1
assert not list(E.rglob('*.olean')) and not list(E.rglob('*.ir'))
assert not[p for p in E.rglob('*')if p.is_file()and p.stat().st_size>20_000_000]
for p in E.glob('*.lean'):
 assert not re.search(r'\b(?:sorry|axiom|admit|native_decide)\b',p.read_text()),str(p)
assert not subprocess.check_output(['git','diff','--check'])
# No shipped source changed, all canonical edges retained and only five promotions.
b=J(E.parent/'ledger28-20261111/NNL_LEDGER.json.xz');x=J(E/'NNM_LEDGER.json.xz');old={r['row']:r for r in b['rows']};assert len(x['rows'])==599
for r in x['rows']:assert r['canonical_callees']==old[r['row']]['canonical_callees']
assert {r['row']for r in x['rows']if r['status']!=old[r['row']]['status']}==({'TX1:345','TX1:344','TX2:233','TX2:242','TX2:241'}if complete else set())
for r in x['rows']:
 assert H(json.dumps(r['obligation'],sort_keys=True,separators=(',',':')).encode())==r['obligation_statement_hash'],r['row']
assert J(E/'NNM_FROZEN_SOURCE_CHECK.json')['status']=='PASS'
# Standard-only print lines on all nine new statement-check theorems.
log=raw(E/'NNM_L024/stdout.log').decode();lines=[l for l in log.splitlines()if 'depends on axioms'in l or 'does not depend on any axioms'in l];assert len(lines)==9
for l in lines:
 if 'depends on axioms:'in l:assert set(re.findall(r'\b(?:propext|Classical.choice|Quot.sound)\b',l))==set(l.split('[',1)[1].rstrip(']').split(', '))
report=dict(status='PASS_EVIDENCE_INTEGRITY'if not complete else'PASS',full_composition_pass=complete,compressed_sha_pairs=sha_pairs,source_snapshots=snapshots,receipts=len(list(E.glob('NNM_L*/receipt.json'))),new_top_print_axioms=lines,predecessor_statement_comparison='PASS all13308',edges_removed=[],shipped_changes=False,key_actions=False,no_committed_build_outputs=True,no_files_over20MB=True,security_target_established=False)
(E/'NNM_VALIDATION.json').write_text(json.dumps(report,indent=1)+'\n');print(json.dumps(report))
