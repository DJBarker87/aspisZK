"""Final local reporting from retained receipts; never a proof/closure producer."""
from pathlib import Path
import json,hashlib,lzma,shutil,subprocess
E=Path(__file__).resolve().parent
H=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
def write(n,x):(E/n).write_text(json.dumps(x,indent=1)+'\n')
assert not(E/'NMP_CLIENT_ACTIVE').exists(),'Active client: do not finalize'
rs={c:[json.loads(p.read_text())for p in sorted(E.glob('NMP_'+c+'[0-9][0-9][0-9]/receipt.json'))]for c in ['K','L']}
assert len(rs['K'])==100 and len(rs['L'])==80,{c:len(v)for c,v in rs.items()}
audit=json.loads((E/'NMP_AUDIT.json').read_text());assert audit['raw_all_standard']
assert json.loads((E/'NMP_FINAL.json').read_text())['status']=='PASS_FINAL'
modules=json.loads((E/'NMP_MODULES.json').read_text())
for c,records in rs.items():
 for r in records:
  limits=r['limits'];assert limits['memory.high']=='6442450944'and limits['memory.max']=='8589934592'and limits['memory.swap.max']=='0'and limits['pids.max']=='64',r['attempt']
  assert str(r['swaps'])=='0',r['attempt']
  if c=='K':
   a=r['attempt'];assert json.loads((E/(a+'-graph-check.json')).read_text())['graph_matches_frozen']
   assert json.loads((E/(a+'-lock-check.json')).read_text())['unchanged']
# Current accepted proof sources must exactly match their successful snapshots.
for m,rel in modules['selected_receipts'].items():
 r=E/rel;assert json.loads(r.read_text())['exit_status']==0
 assert (E/'NMP_generated'/(m+'.lean')).read_bytes()==(r.parent/'sources/NMP_generated'/(m+'.lean')).read_bytes(),m
# No shipped repository path is part of this worker's changes.
changed=subprocess.check_output(['git','diff','--name-only','HEAD'],text=True).splitlines()
assert all(x.startswith('evidence/tx1-observed3-20261110/')for x in changed),changed
attempts=[json.loads(l)for l in(E/'NMP_ATTEMPTS.jsonl').read_text().splitlines()]
waits=[x for x in attempts if x.get('kind')=='wait']
summary=dict(target_established=False,closed_rows=[],qualified_rows=[],budgets=dict(kani=dict(used=100,limit=100),lean_support=dict(used=80,limit=80),extraction=dict(used=0,limit=0)),wait_records=len(waits),new_source_modules=modules['modules'],new_support_roots=modules['roots'],raw_roots=audit['raw_roots'],scan_modules=audit['scan_modules'],raw_all_standard=True,swaps=0,max_peak_rss_kib={c:max(int(r['peak_rss_kib'])for r in rows)for c,rows in rs.items()},receipts='NMP_K*/receipt.json and NMP_L*/receipt.json',source_revision='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387',pool_revision='b936275465',pool_elf_pin='e0e49c344d35575116c0359450315ea4334bfb03006551727f67c04a8cfe09dc',shipped_repository_files_changed=False,elf_rebuild=False,artifact_pins='Inherited; not freshly reproduced',trust_rows_added=[],retained_trust='Existing runtime, std/allocator and P6/D188 contract semantic transport; reclassified, never removed')
write('NMP_SUMMARY.json',summary)
closed=json.loads((E/'NMP_CLOSED.json').read_text());closed['status']='OPEN_PARTIAL_NATIVE_AND_SOURCE_SUPPORT';closed['source_support']=modules['roots'];write('NMP_CLOSED.json',closed)
delta=json.loads((E/'NMP_LEDGER_DELTA.json').read_text());delta['status']='FINAL_ZERO_DELTA';write('NMP_LEDGER_DELTA.json',delta)
clauses=json.loads((E/'NMP_CALLER_CLAUSES.json').read_text());clauses['status']='FINAL_PARTIAL_CALLER_SUPPORT_NO_ROOT'
for x in clauses['clauses']:
 if x['name']=='rhoBlock and rhoReduction':
  x['status']='SOURCE_REDUCTION_SUPPORT_BLOCK_DOMAIN_OPEN';x['new_support']='NMP_RhoReduction179.source and same_block construct K for the SAME block without a sampler-success hypothesis';x['remaining']='Construct the SAME three-call rhoBlock from bounded/readable primitive runtime laws and native prepare prefix; install all caller domains'
write('NMP_CALLER_CLAUSES.json',clauses)
with(E/'NMP_REMAINING.md').open('a')as f:f.write('''
## Final budget boundary
All100 Kani and80 Lean/support scopes were consumed;0 extractions. This is not a stop caused by the open child or by Kani exhaustion alone. Independent source/certificate and rejection-resource work continued, followed by the coherent final audit. No candidate root or promotion is emitted.

| Member | Native work still required | Lean/composition still required |
|---|---|---|
|TX1:137|Full borrowed Prefix allocation/extent coverage; returning immutable-input frame; H/padding/ghost representation association; complete same-world producer|Full-strength136 child law at SAME reached arguments; canonical physical/call/ordered-effect interpretation; combine all universal native windows without endpoint-success premises|
|TX1:087|Complete actual-parent relation for allocation primitive interpretation, all child outcome arms, retained proof/logical views, full g/Prepared ownership frames|SAME closed child installations and full137 law; every179 bf caller clause, including opening/query effects and deployed configuration; no arbitrary-success domain strengthening|
|TX1:179 caller|Native087 prefix must produce the SAME arguments/readable views and runtime digest-call domains|Rho reduction factory is source support only; opening packet and SAME three-call hash blocks remain. Query error/fail/div companions are available but complete effect/physical association is not installed|
|Gate/release|No new native row producer exists to admit; this audit cannot supply one|Standard raw axioms/import coherence do not discharge source refinement or the100-bit per-attempt release contract|

Some mathematical opening-packet construction may be pursued in a subsequent Lean budget; it is not declared impossible or silently converted to Kani work. Both parent members still require new native coverage, and current conditional folds are never substituted for their full ledger obligations. Target not yet established.
''')
text=f'''# NMP final handoff

Target not yet established. TX1:137 and TX1:087 remain OPEN; ledger24 stays581 CLOSED /0 QUALIFIED /18 OPEN. No candidate root, promotion or new trust row.

The actual frozen verify_observed was checked at the original13831-byte window with arbitrary payload/typed owned fields. Ten return-field projections have matched reply/argument/write-footprint controls, and the None-route rename pair passes. The retained928-byte window has its own positive/corruption pair. These are local relations, not a complete native producer. Prepare was exercised at57607 bytes with free137/179 replies and explicit typed-array mutable byte generation after the heap-subwindow contract attempt crashed and was left unadmitted; see NMP_NATIVE_FINAL.json for every result and failure.

Source support includes transcription/reached-prefix folds, correct stopped/rejected resource-frontier support, SAME expansion/canonicality/query-outcome helpers, and SAME-block rho-certificate construction using existing closed pass/digit laws. Full physical interpretation, borrowed-type coverage, representation erasure and179 caller-domain installation remain open. NMP_CUTMAP.md and NMP_REMAINING.md specify each gap; no weak NLI packet or XRn join kit is used as credit.

Validation:100 Kani,80 Lean/support,0 extraction; all scopes capped6G/8G/0 swap/64 tasks. Every Kani graph/lock check is retained. Raw ax2 checked{audit['raw_roots']} roots (new support plus AspisR1.RPx_Deployed.deployed), all standard axioms;{audit['scan_modules']} modules scanned with0 dangling/duplicate/import mismatches; eight fidelity fixtures. Collector disagreements, if any, are retained in NMP_AUDIT.json. Source/dependency/tool pins and exact targets, exits, wall/RSS/swap and #print axioms are in each receipt.

No shipped repository file changed. Release source pins are4bb3b3f51e16b4525f1d10336e2b0bcbbd775387 and Pool b936275465, Pool ELF e0e49c344d35575116c0359450315ea4334bfb03006551727f67c04a8cfe09dc. ELF pins are inherited, not freshly rebuilt. Own cache/exports are retained; no keys or sibling worktrees were touched; no push.

Next deliverable: a full native/canonical physical producer for each parent, exact179 caller installations, and a next-ledger admission. See NMP_CHILD136_GATE_CHECK.json for the read-only child merge snapshot used by the gate. All successful support is explicitly conditional where its native or child-domain clauses remain unproved.
'''
(E/'NMP_HANDOFF.md').write_text(text)
# Rule12: keep only compressed forms of oversized evidence, with original SHA.
for p in list(E.rglob('*')):
 if not p.is_file()or p.stat().st_size<=20*1024*1024:continue
 assert p.suffix!='.xz',('Compressed artifact exceeds20MiB',str(p))
 raw=p.read_bytes();q=Path(str(p)+'.xz');q.write_bytes(lzma.compress(raw,preset=6));assert q.stat().st_size<=20*1024*1024,str(q)
 Path(str(p)+'.sha256').write_text(hashlib.sha256(raw).hexdigest()+'\n');p.unlink()
for p in E.rglob('__pycache__'):shutil.rmtree(p)
assert not[p for p in E.rglob('*')if p.is_file()and p.stat().st_size>20*1024*1024]
print(json.dumps(dict(status='FINAL_REPORTS_WRITTEN',native=100,lean_support=80,closed_rows=0,target_established=False)))
