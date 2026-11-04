"""Collect authoritative raw/fixture/coherence evidence; never promote Pool rows."""
from pathlib import Path
import json,hashlib,collections,re,sys,lzma
E=Path(__file__).resolve().parent;H=lambda b:hashlib.sha256(b).hexdigest()
def raw(p):
 if p.exists():return p.read_bytes()
 data=lzma.decompress(Path(str(p)+'.xz').read_bytes());assert H(data)==Path(str(p)+'.sha256').read_text().strip();return data
J=lambda p:json.loads(raw(p))
def emit_associations(data):
 p=E/'NGK_CERT_ASSOCIATIONS.json';b=(json.dumps(data,indent=1)+'\n').encode();h=H(b);q=Path(str(p)+'.xz');pin=Path(str(p)+'.sha256')
 if len(b)>20000000:
  if not (q.exists() and pin.exists() and pin.read_text().strip()==h):q.write_bytes(lzma.compress(b,preset=6));pin.write_text(h+'\n')
  assert H(lzma.decompress(q.read_bytes()))==h;p.unlink(missing_ok=True)
 else:p.write_bytes(b)

manifest=J(E/'NGK_AUDIT_ROOTS.json');results=[]
for i,group in enumerate(manifest['groups']):
 r=J(E/f'NGK_audit/batch{i}/proof{i}.json');assert r['exit_status']==0
 assert [x['root'] for x in r['results']]==group
 results+=r['results']
assert collections.Counter(r['root'] for r in results)==collections.Counter(manifest['roots'])
assert all(set(r['walked_axioms'])<={'propext','Classical.choice','Quot.sound'} for r in results)
fixtures=J(E/'NGK_audit/fixtures/fixtures.json')['results'];assert len(fixtures)==8 and all(r['equal'] for r in fixtures)
assert [r['walked_axioms'] for r in fixtures]==[['NEP_Planted.matchAx'],['NEP_Planted.privateAx'],['NEP_Planted.proofAx'],['NEP_Planted.auxAx'],[],[],[],[]]
fixture_pin=J(E/'NGK_L056/NGK_ProofDriver_BINARY_PIN.json')
for i in range(58,58+len(manifest['groups'])):assert J(E/f'NGK_L{i:03}/NGK_ProofDriver_BINARY_PIN.json')==fixture_pin
scan=[json.loads(l) for l in (E/'NGK_LOADED_scan.jsonl').read_text().splitlines()]
assert all(not r['dangling'] and not r.get('duplicate_owners',[]) and r['imports_match'] for r in scan)
summary=dict(status='PASS',modules=len(scan),declarations=sum(r['declarations'] for r in scan),references=sum(r['edges'] for r in scan),dangling=0,incompatible_owners=0,import_mismatches=0,compatible_cached_replicas=sum(len(r.get('cached_replicas',[])) for r in scan),receipt='NGK_L057/receipt.json',artifact='NGK_LOADED_scan.jsonl',artifact_sha256=H((E/'NGK_LOADED_scan.jsonl').read_bytes()),independent_expected_imports='NGK_EXPECTED_IMPORTS.jsonl',baseline_sha256=H((E/'NGK_EXPECTED_IMPORTS.jsonl').read_bytes()),baseline_origin='accepted NGJ committed baselines plus source-derived NGK import lists, never candidate scan',legacy_bad_owner_modules_loaded=[r['module'] for r in scan if r['module'] in ['S2SdkOwnedGuardBodyV1','PreparedFromQmSourceBridge','S1SemanticPhaseV1']])
assert not summary['legacy_bad_owner_modules_loaded'];(E/'NGK_SCAN.json').write_text(json.dumps(summary,indent=1)+'\n')
(E/'NGK_AUDIT.json').write_text(json.dumps(dict(status='PASS',authoritative='private importAll checked-kernel raw ax2 traversal, including opaque proof bodies',combined_import='NGK_COMBINED_IMPORT',headline=manifest['headline'],root_count=len(results),roots=results,standard_axioms_only=True,collect_disagreements=[r for r in results if not r['equal']],fixture_results=fixtures,fixture_binary=fixture_pin,all_batches_same_binary=True,walker=J(E/'NGK_WALKER_CONFORMANCE.json'),full_scan='NGK_SCAN.json',cold_release_replay=False,formal_release=False),indent=1)+'\n')
if '--audit-only' in sys.argv:
 print(len(results),'raw roots;',len(scan),'coherent modules; statement review pending')
 sys.exit(0)
# Source theorem names were inventoried BEFORE loading; associate exact types and
# actual module ownership from the independent 33 statement receipts.
entries=[]
for i in range(33):
 p=E/f'NGK_L{78+i:03}/stdout.log';rc=J(p.parent/'receipt.json');assert rc['exit_status']==0
 entries += [json.loads(l.split('NGK_CERT_ENTRY ',1)[1]) for l in raw(p).decode().splitlines() if 'NGK_CERT_ENTRY ' in l]
statements=J(E/'NGK_STATEMENT_MANIFEST.json')['records']
assert collections.Counter(e['name'] for e in entries)==collections.Counter(r['name'] for r in statements)
for r in statements:
 e=next(e for e in entries if e['name']==r['name']);assert e['owner']=='NGK_'+r['source_module']
 assert r['name'] in manifest['roots']
emit_associations(dict(status='PASS',explicit_theorems=len(entries),entries=entries,all_standard_printed_axioms=True,all_raw_audited=True,source_inventory='NGK_CERTIFICATES.json'))
(E/'NGK_LEDGER_DELTA.json').write_text(json.dumps(dict(status='HEADLINE-COHERENT POOL FOREST; NO ROW PROMOTION',basis='NDT semantics, NGJ 599 verifier rows unchanged; Pool consumer outside that basis',rows=[],composed_rows_added=0,closed_by_this_job=0,before=dict(Pool_production_association='OPEN',B='OPEN',D='OPEN'),after=dict(Pool_production_association='OPEN',B='OPEN',D='OPEN'),coherence_before=dict(joint_import='FAIL',dangling=650,import_baseline_failures=548),coherence_after=summary,assumptions_discharged=[],assumptions_added=[],assumptions_removed=[],trust='existing P6/D188 option-A semantic transport, SDK/std/allocator/ABI/compiler/Aeneas/source-to-ELF, RuntimePersistence, digest/H, RuntimeReturnData nonempty1..1024, RuntimeMemcmp and cryptographic assumptions retained; reclassification not removal',next='NGG committed B/D production-prefix certificates must receive the SAME canonical retarget before admission; no uncommitted sibling WIP imported'),indent=1)+'\n')
print(len(results),'raw roots;',len(entries),'explicit theorem associations;',len(scan),'modules; no Pool rows promoted')
