from pathlib import Path
import json,hashlib,lzma,re,subprocess
E=Path(__file__).resolve().parent
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
verify=json.loads((E/'NKU_EXPORT_VERIFY.json').read_text());assert verify['pass_all']
selected=json.loads((E/'NKU_SELECTED_SOURCES.json').read_text())
for m,row in selected.items():
 p=E/(m+'.lean');assert sha(p)==row['sha256']
 s=p.read_text();assert not re.search(r'\b(sorry|admit|native_decide)\b|^\s*axiom\s|set_option\s+max(RecDepth|Heartbeats)',s,re.M),m
 assert all(n in s for n in ['#print axioms']) or not re.search(r'^theorem\s',s,re.M),m
pins=json.loads((E/'NKU_INPUT_PINS.json').read_text())
for x in pins:assert sha(Path(x['path']))==x['sha256'],x['path']
initial=subprocess.check_output(['git','rev-parse','c82f94b1558^'],text=True).strip()
changed=subprocess.check_output(['git','diff','--name-only',initial,'HEAD'],text=True).splitlines()
assert changed and all(n.startswith(str(E.relative_to(Path.cwd()))+'/') for n in changed)
assert not subprocess.check_output(['git','diff',initial,'HEAD','--','crates','programs'])
receipts=sorted((json.loads(p.read_text()) for p in E.glob('NKU_[LKE]*/receipt.json')),key=lambda x:x['attempt'])
lean=[x for x in receipts if x['kind']=='lean'];kani=[x for x in receipts if x['kind']=='kani']
assert len(lean)<=150 and len(kani)<=10 and all(x['kind']!='extract' for x in receipts)
for r in receipts:
 assert r['limits']=={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'},r['attempt']
 assert str(r['swaps'])=='0',r['attempt']
 assert r['env']['CARGO_TARGET_DIR'].endswith('/codex-cx-tx2-resume2-20261109/NKU_target')
 admission=json.loads((E/(r['attempt']+'-admission.json')).read_text());assert admission['exit']==0 and admission['reservation']['allowed'] is True
 disk=json.loads((E/(r['attempt']+'-disk.json')).read_text());assert disk['free_bytes']>=40_000_000_000
base=E.parent/'ledger19-20261108/NKN_LEDGER.json.xz';raw=lzma.decompress(base.read_bytes());ledger=json.loads(raw)
row=next(r for r in ledger['rows'] if r['row']=='TX2:124')
assert row['status']=='OPEN'
caller_requirements=['proof length57607','public length0..1880','Variant::S2','SAME actual Allocator Reservation; every error/abort prefix retained']
proposal=dict(row='TX2:124',function=row['function'],frozen_body_sha256=row['frozen_body_sha256'],proposed_status='CLOSED',status='CANDIDATE_PENDING_LEDGER_GATE',route='direct hybrid P6; (y)/(ai)/(aq)/(aq)(5), option A',parent_state='NKU.State',native_G='NKU_ParentFold.G',source_root='NKU_ParentFold.source',cohort_root='NKU_ParentFold.cohort',child_clauses='NKU_ParentFold.clauses',incoming_native_scope=caller_requirements,scope_review='NKU_NATIVE_INPUTS.md',native_cuts='NKU_NATIVE_CUT_TABLE.json',constructor_review='NKU_TERMINAL_CARRIER_REVIEW.md',audit='NKU_AUDIT.json',combined_import='NKU_COMBINED_IMPORT.lean',new_trust_rows=[],trust_reclassification='Existing option-A P6/D188 native contract semantic transport; not removal',abort_scope='Exact returning Rust Results and chronological native abort prefixes under existing std/Allocator/runtime items; no totality claim')
(E/'NKU_CLOSED.json').write_text(json.dumps(dict(rows=[proposal],target='TX2:124',status='CANDIDATE_PENDING_LEDGER_GATE',target_established=False,credit='No authoritative ledger promotion made'),indent=2)+'\n')
counts=dict(CLOSED=553,QUALIFIED=0,OPEN=46,total=599)
(E/'NKU_LEDGER_DELTA.json').write_text(json.dumps(dict(baseline=str(base),baseline_xz_sha256=sha(base),baseline_raw_sha256=hashlib.sha256(raw).hexdigest(),before=counts,after=counts,proposed_after=dict(CLOSED=554,QUALIFIED=0,OPEN=45,total=599),promotions=[],proposed_promotions=['TX2:124'],target_status='CANDIDATE_PENDING_LEDGER_GATE',credit='Waits for next authoritative ledger gate; incoming caller native-scope clause remains explicit'),indent=2)+'\n')
summary=dict(status='PASS',target='TX2:124 parent fold',source_revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),source_tree_dirty=True,budget=dict(lean_used=len(lean),lean_limit=150,kani_used=len(kani),kani_limit=10,extraction_used=0,extraction_limit=0),support_jobs=len(receipts)-len(lean)-len(kani),combined_source_sets=2,modules=len(selected),roots=verify['roots'],raw_axioms='subset of propext, Classical.choice, Quot.sound; every walk equals collectAxioms',reused_roots=verify['reused_roots'],new_roots=verify['new_roots'],unchanged_old_closure_objects=verify['unchanged_old_closure_objects'],fixtures=8,scan=dict(modules=verify['scan_modules'],exit=0,dangling=0,owner_conflicts=0,import_mismatches=0),attempts=[dict(attempt=r['attempt'],target=r.get('module'),kind=r['kind'],exit=r['exit_status'],wall_seconds=r['wall_seconds'],peak_rss_kib=r['peak_rss_kib'],swaps=r['swaps'],source_revision=r['source_revision'],receipt=r['attempt']+'/receipt.json') for r in receipts],source_validation='all selected source hashes match successful receipts; forbidden proof forms/resource overrides absent; input pins unchanged; no shipped-source diff',native_credit_scope=caller_requirements,release_claim=False)
(E/'NKU_AUDIT.json').write_text(json.dumps(summary,indent=2)+'\n')
(E/'NKU_SOURCE_VERIFICATION.json').write_text(json.dumps(dict(selected_modules=len(selected),source_hashes_match=True,input_pins_match=True,shipped_source_changes=False,all_changes_in_own_evidence=True,initial_revision=initial,source_revision=summary['source_revision']),indent=2)+'\n')
(E/'NKU_FAILING_STEP.md').write_text('''# NKU current failing step

No failing owned parent-fold step remains under the explicit native input scope. NKU_ParentFold.source/cohort/clauses and the final combined/raw/NFX gates pass. Historical failures and replacements are in NKU_FINDINGS.md.

Credit is pending the next ledger gate. C01 consumers must establish proof57607/public<=1880 from their actual caller context; tx2_common has no intrinsic public-size guard. The general source equation must not be used to widen native credit. This incoming clause is owned by the consuming parent, not replaced by a root success premise here. The100-bit headline remains not established.
''')
(E/'NKU_REMAINING.md').write_text('''# NKU remaining disposition

TX2:124 has one complete native-parent-G candidate, pending the next authoritative ledger gate. Actual counts remain553 CLOSED /0 QUALIFIED /46 OPEN /599. Global100-bit target not yet established.

| Owned member | Final disposition / remaining work |
|---|---|
| header1 and earlier guards | Complete: actual live iterator/next byte in ONE State, all reject/abort prefixes; HeaderPrefix/End/State and FineHeader. No missing native window. |
| digests2–4 | Complete within proof57607/public<=1880/checkpoint1768: actual slices/chunks, reply/byte frames, DigestState. No SHA unwind/new trust. Incoming proof/public extent belongs to consumer context. |
| roots5–7 | Complete single raw32 steps, SAME backing/Reader80→176; RawAt/FineRoots. |
| fields8–12 | Complete single E/K steps and domains, SAME decoded slots/Reader176→320; FineGamma/EAt/KAt/Offsets. |
| query13–34 | Complete one raw4 step per word, actual8/8/6 windows and SAME Reader320→408; FineWords/WordsAt/CallerScope and three joins. |
| validator35 | Complete CLOSED child at SAME22 words, Rust Err/no-suffix retained. |
| semantic36 | Complete CLOSED child/full writeback/SAME cursor408→568, preceding frame retained. |
| z/claim/rhs/power37–43 | Complete single state steps and actual domains/Reader568→712; FineZ and Offsets. |
| filled44 | Complete SAME actual Reservation/owner/zero64 and Err Allocation branch; no fresh success flag. |
| weights45 /64 nested reads | Complete CLOSED owned child on that SAME Vec64, output/frame/cursor1736 and first-error cleanup. |
| tail/Box/pair/cleanup | Complete native returning value/owner/drop scope under retained (aa)/(an)/(au); emitted and cohort cuts are explicitly separate types. No variant-only promotion from K045. |
| combined/raw/NFX/export | PASS:86 modules/124 roots, standard axioms,8 fixtures,16339-module zero-issue scan; first99 walks reused only after32917 unchanged dependency-object hashes verified. Two combined source sets; no unchanged full regression. |

No owned Lean-only or Kani-only step remains. No new Kani window was needed, so0/10 Kani and0 extraction.133/150 actual Lean invocations (labels include separately accounted support jobs); no proof count is treated as ledger credit. Further compiler calls would not close another owned member. The remaining external action is the lead's ledger admission/caller-domain review; NKO/TX2:065 must establish its incoming native proof/public extent before consuming C01. No unrestricted larger-public native claim is made. No sibling worktree/candidate, shipped file, wallet/key, trust row, protocol or security metric was changed.
''')
print(json.dumps(dict(artifacts='written',modules=len(selected),roots=verify['roots'],lean=len(lean),support=len(receipts)-len(lean),native_candidate='TX2:124',ledger_promotions=0)))
