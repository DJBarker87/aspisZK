from pathlib import Path
import json,hashlib,lzma,re,subprocess
E=Path(__file__).resolve().parent
receipts=[json.loads(p.read_text()) for p in sorted(E.glob('NJJ_[LKE][0-9][0-9][0-9]/receipt.json'))]
ks=[r for r in receipts if r['kind']=='kani'];assert len(ks)==80
pairs=[(5,6),(7,8),(9,10),(11,12),(13,14),(17,18),(19,20),(21,22),(23,24),(26,27),(28,29),(30,31),(32,33),(34,35),(36,37),(38,39)]+[(n,n+1) for n in range(40,60,2)]+[(60,61),(63,64),(66,67),(70,71),(74,75),(76,77),(78,79)]
extra={60:[62],63:[65],66:[68,69],70:[72,73]};table=[]
for pos,neg in pairs:
 a=f'NJJ_K{pos:03d}';controls=[neg]+extra.get(pos,[])
 r=json.loads((E/a/'receipt.json').read_text());assert r['exit_status']==0
 for n in controls:
  p=E/f'NJJ_K{n:03d}';assert json.loads((p/'receipt.json').read_text())['exit_status']!=0 and 'VERIFICATION:- FAILED' in (p/'stdout.log').read_text() and 'timed out' not in (p/'stdout.log').read_text()
 table.append(dict(harness=r['module'],positive=a,controls=[f'NJJ_K{n:03d}' for n in controls],source_hashes=r['source_hashes'],domain_status='local component/cut only; positive root OPEN'))
(E/'NJJ_NATIVE_CERTIFICATES.json').write_text(json.dumps(table,indent=2)+'\n')
text=['# NJJ certificates','','TX2:065 OPEN; target not yet established. No row/count promotion. Native semantic transport is P6/D188 option-A trust reclassification, never removal. All local positives below have matched controls; K080 is an unrun extra guard and adds no credit.','','| Frozen/staged native cut | PASS | Matched semantic FAIL controls |','|---|---|---|']
for row in table:text.append('| '+row['harness']+' | '+row['positive']+' | '+', '.join(row['controls'])+' |')
text+=['','All per-run graphs match the frozen lock and deployed feature closure; all post-run lock hashes are unchanged. Same-harness names are retained. No contracts, stub_verified, writable static, field-product proof, Option<fn>-dependent result or custom copy stub. Exact KMX sources and patch are checked each time.','','The native-to-cut transcriptions are NJJ_Cuts (pending payload/end and weights), NJJ_Constructors (all Prepared/Accumulator fields), and the source-body specialization NJJ_Common. Native row windows are lifted by NJJ_RowWindow over supplied KMX laws; NJJ_PendingStep derives the complete typed step from the literal emitted body; NJJ_Pending supplies finite induction. NJJ_ResumeDomains derives every entered read bound and complete byte/cursor/frame Result. NJJ_Value projects the actual emitted value at arbitrary index to a single row, and NJJ_Flush gives every output cell and canonicality. These lemmas do not invent missing parent argument observations; see REMAINING.','','Full-source inputs are retained once by sha256 in NJJ_inputs and NJJ_INPUTS_INDEX.json; each receipt lists exact source hashes, dependency objects, source revision, cap, time/RSS/swap and axioms. No failed Lean version is selected.','','Copy-dependent positives use the supplied exact patch and the controls in this table. Source/domain qualifications remain those of NJJ_CUTS.md. In particular, the checksum native scope requires proof57607/public≤1880; its unrestricted-root domain is not proved. Receiver/backing observations missing from selected parent cuts remain OPEN, not extra assumptions.']
(E/'NJJ_CERTIFICATES.md').write_text('\n'.join(text)+'\n')
for r in ks:
 a=r['attempt'];g=json.loads((E/(a+'-graph-check.json')).read_text());lock=json.loads((E/(a+'-lock-check.json')).read_text());assert g['graph_matches_frozen'] and lock['unchanged']
modules=json.loads((E/'NJJ_MODULES.json').read_text()) if (E/'NJJ_MODULES.json').exists() else []
selected=[]
for m in modules:
 matches=[r for r in receipts if r['kind']=='lean' and r['module']==m and r['exit_status']==0];assert matches,m
 r=matches[-1];key='NJJ_generated/'+m+'.lean';assert hashlib.sha256((E/(m+'.lean')).read_bytes()).hexdigest()==r['source_hashes'][key],m
 assert all('sorryAx' not in line for line in r['print_axioms']),m
 selected.append(dict(module=m,attempt=r['attempt'],source_sha256=r['source_hashes'][key],print_axioms=r['print_axioms']))
(E/'NJJ_SELECTED.json').write_text(json.dumps(selected,indent=2)+'\n')
baseline='evidence/ledger13-20261107/NIU_LEDGER.json.xz';uncompressed_hash=Path('evidence/ledger13-20261107/NIU_LEDGER.json.sha256').read_text().strip()
(E/'NJJ_LEDGER_DELTA.json').write_text(json.dumps(dict(baseline=baseline,baseline_uncompressed_sha256=uncompressed_hash,before=dict(CLOSED=432,OPEN=167,QUALIFIED=0),after=dict(CLOSED=432,OPEN=167,QUALIFIED=0),promotions=[],closed_rows=[],closed_edges=[],target='TX2:065',target_status='OPEN',new_trust_rows=[],gate='component audit only; credit waits for next authoritative ledger gate'),indent=2)+'\n')
(E/'NJJ_CLOSED.json').write_text(json.dumps(dict(frozen_revision='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387',headline='AspisR1.RPx_Deployed.deployed',functions=[],target='TX2:065',status='OPEN',security_target_established=False,closed_rows=[],closed_edges=[],admitted_rows=[],new_trust_rows=[],local_certificates='NJJ_NATIVE_CERTIFICATES.json',model_results='NJJ_SELECTED.json',remaining='NJJ_REMAINING.md',credit='No promotions; wait for the next authoritative ledger gate'),indent=2)+'\n')
compact=[{k:v for k,v in r.items() if k!='deps_fingerprint'} for r in receipts];raw=json.dumps(compact,sort_keys=True).encode();(E/'NJJ_RELEASE_RESULTS.json.xz').write_bytes(lzma.compress(raw,preset=6));(E/'NJJ_RELEASE_RESULTS.json.sha256').write_text(hashlib.sha256(raw).hexdigest()+'\n')
print(json.dumps(dict(kani_slots=len(ks),positive_pairs=len(table),semantic_controls=sum(len(r['controls']) for r in table),selected_modules=len(selected),new_closed_rows=0)))
