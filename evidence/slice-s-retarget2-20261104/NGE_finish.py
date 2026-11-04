"""Final exact-budget/resource/source/assumption receipt and substantive handoff."""
from pathlib import Path
import json,re,subprocess,hashlib,lzma,collections,sys
sys.dont_write_bytecode=True
E=Path(__file__).resolve().parent;R=E.parents[1];J=lambda p:json.loads(p.read_text())
rs={p.parent.name:J(p) for p in E.glob('NGE_L*/receipt.json')};expected={f'NGE_L{i:03}' for i in range(1,111)};assert set(rs)==expected
assert len((E/'NGE_ATTEMPTS.jsonl').read_text().splitlines())==110
for a,r in rs.items():
 ad=J(E/(a+'-admission.json'));assert ad['exit']==0 and ad['reservation']['allowed'] is True
 assert str(r['swaps'])=='0';assert '-M7000' in r['command'] or r['kind'] in ['audit','link']
 if r['exit_status']!=0:assert a in ['NGE_L028','NGE_L097']
config=J(E/'NGE_L110.json');delta=J(E/'NGE_LEDGER_DELTA.json');audit=J(E/'NGE_AUDIT.json');inventory=J(E/'NGE_DECLARATION_INVENTORY.json');cert=J(E/'NGE_CERT_CHECK.json')
assert audit['root_count']==3703 and inventory['selected_names']==257
assert J(E/'NGE_TESTS.json')['status']=='PASS' and J(E/'NGE_PACK.json')['status']=='PASS'
budget=dict(Lean_charged=110,Lean_budget=110,Kani=0,extraction=0,remaining=0,successful=sum(r['exit_status']==0 for r in rs.values()),failed=['NGE_L028','NGE_L097'],scope_wall_seconds=sum(r['wall_seconds'] for r in rs.values()),peak_rss_kib=max(int(r['peak_rss_kib']) for r in rs.values()),all_swaps_zero=True,one_own_scope_at_a_time=True,cap=dict(MemoryHigh='6G',MemoryMax='8G',MemorySwapMax=0,TasksMax=64,Lean_M=7000),no_timeout_or_memory_kill=True,no_unchanged_full_replay=True,source_revision=subprocess.check_output(['git','rev-parse','HEAD'],cwd=R,text=True).strip(),print_axioms='All successful new top theorem/raw results: subset of propext, Classical.choice, Quot.sound. Failed L028 sorryAx output excluded; eight planted/mutation fixtures are intentional.',stages=dict(focused_module_attempts=31,combined_and_driver_attempts=5,fixtures_and_scan=2,raw_audit_groups=58,kernel_certificate_inventory_attempts=14))
(E/'NGE_BUDGET.json').write_text(json.dumps(budget,indent=1)+'\n')
frozen='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387';target=J(E/'NGE_TARGET.json')
for d in ['crates','programs']:
 assert subprocess.check_output(['git','rev-parse','HEAD:'+d],cwd=R,text=True).strip()==target['shipped_trees'][d]['frozen_git_tree']
 assert not subprocess.check_output(['git','status','--porcelain','--',d],cwd=R,text=True).strip()
roots_closed=sum(r['status']=='CLOSED' for r in delta['S_roots']);before=delta['S_before'];after=delta['S_after'];maxrss=budget['peak_rss_kib'];failed_text='NGE_L028 failed at helper-name resolution; NGE_L029 corrected only the map_err owner qualification, using the existing axiom-free NFY_OwnerTransport.map_err_transport. L097 failed because ModuleIdx has no Repr instance; L098 uses the pinned toolchain ModuleIdx.toNat accessor and the inventory is regrouped into 13 successful parts without losing a name. No timeout, memory kill, raised cap, extraction, Kani, Rust or SBF build occurred.'
text=f'''# NGE canonical chain A handoff

**{len(delta['promotions'])} additional S rows CLOSED; S {after.get('CLOSED',0)}/97 CLOSED, {after.get('QUALIFIED',0)} QUALIFIED, {roots_closed}/7 roots CLOSED. Target not yet established.** Branch codex/cx-slice-s-retarget2-20261104. No push or merge. NGE_LEDGER_DELTA.json is an additive S-only delta on NFY; the corrected inventory basis remains 599, including concurrent D/Pool work. No stale global count is substituted.

## Claim established

All 30 chain A auxiliaries and their nonreused closure are coherently retargeted: NEE (1), NEJ (5), NEL (7), NEM (7), NEQ (8), NBN (2). NGE_PROVENANCE.json records exact committed source pins, before/after bodies, module/namespace maps and line ranges. NGE_generate.py --check reproduces them. Eight S2K dependencies reuse byte-identical non-import JHb bodies in NFY, with hashes and NGE_SHARED_REUSE_DIFFS.json; no shared owner is redefined. Only imports, qualified identifiers and one emitted map_err helper qualification change. No domain, carrier, quantifier, failure event, bound or hypothesis is strengthened or weakened.

NGE_COMBINED_IMPORT loads the actual AspisR1.RPx_Deployed.deployed, NFX admitted forest, NFY packet forest and chain A together. The raw ax2 walker audits **{audit['root_count']:,} roots**, with standard axioms only; the exact same proof-driver binary passes all eight planted/mutation fixtures. The full scanner covers **{audit['scan']['modules']:,} modules / {audit['scan']['declarations']:,} declaration entries / {audit['scan']['edges']:,} references**, with zero dangling references, incompatible owners or import mismatches; {audit['scan']['compatible_cached_replicas']:,} compatible cached replicas disclosed. The walker objects and driver diffs are pinned by NGE_WALKER_CONFORMANCE.json. See NGE_AUDIT.json and NGE_SCAN.json.

NGE_certificates.py recursively enumerates EVERY theorem record in all 89 selected historical certificates: 19,176 records, 257 distinct names. NGE_DECLARATION_INVENTORY.json independently reads every name's actual ConstantInfo type and owning module from the compiled combined environment: {inventory['found']} present, {inventory['absent']} absent, no owner mismatch. All present selected declarations are direct raw roots. NGE_CERT_CHECK.json checks the complete inventory, not the old 88-root aggregate. NGE_checks.py preserves selected-callee denial propagation. NGE_REPLAY_NFX_LEDGER.json reproduces the unchanged historical NFX builder exactly in a private sparse-read sandbox; its 587-row baseline is historical, not the corrected inventory. NGE_TESTS.json records positive gates and 11 rejected evidence mutations.

## Remaining and retained assumptions

All {len(delta['remaining_qualified_S'])} remaining QUALIFIED rows, every exact missing declaration, and selected-callee consequences appear in NGE_REMAINING.md / NGE_CERT_CHECK.json. Missing declarations are chain B NEX/NEY auxiliaries only; none belongs to chain A. These require Lean retarget/replay, **0 Kani and 0 extraction**. No chain B or session A source/worktree was changed. Three S roots remain QUALIFIED; use the exact S_roots records in the delta.

No trust row was added or removed. P6/D188 option-A native contract semantic transport is retained/reclassified, never removed. RuntimePersistence, RuntimeReturnData (nonempty 1..1024; ASR8 792), RuntimeMemcmp, SDK/std/allocator/ABI/compiler/source-to-ELF and the cryptographic assumptions remain explicit. L154 stays a statement parameter; digest/error are op43/op44. This supplies cached canonical certificate coherence, not a new native pass, a cold release replay, deployment proof or the 100-bit per-attempt conclusion. Outside this slice remain D/Pool joins, L159/L181, L187 and L188 as governed by the current lead ledger.

## Validation, budget and incidents

**110/110 charged formal/audit slots, 0 Kani, 0 extraction.** There are 108 successful scopes and two failed elaborations. Peak RSS **{maxrss:,} KiB**, all swaps 0; summed scope wall **{budget['scope_wall_seconds']:.3f} s**. Every launch has exit-0 AND allowed:true admission and uses 6G high / 8G max / swap0 / Tasks64; Lean -M7000. Exact target, command, exit, wall/RSS/swap, source revision/hash, direct/Aeneas object pins and #print axioms are in NGE_ATTEMPTS.jsonl and the linked receipts. All new top theorems have standard-only audits, or none. {failed_text}

The worker-owned Python sparse reader initially mishandled Python's locale encoding marker; the retained first receipt and corrected reader show that no validator predicate changed. Repeated large root/import inputs are retained once, with per-receipt SHA256 references in NGE_PACK.json. The final 14 slots comprise one failed meta-code elaboration and 13 successful complete kernel-loaded certificate inventory parts; no formal budget remains. No row is promoted merely from a compile, module-path association or renamed theorem.

## Reuse, frozen source and artifacts

Owned cache /home/dombarker/project-offloads/codex-cx-slice-s-retarget2-cache-20261104; workspace /home/dombarker/project-offloads/codex-cx-slice-s-retarget2-20261104. NGE_EXPORT.json and NGE_CLOSURE_PINS.json.xz pin retained exports and the actually resolved closure. For successors put NGE_exports_20261104 first, then NFY_exports_20261104, NFY_priority, coherent SInt2 root/objects, own fallback and Lean library. NGE_CACHE_IMPORTS.json.xz pins the copied 71,254-file / 30,734,187,166-byte seed. Separate copies of retained hardlinked views exceeded the preferred 20 GB; no cache was deleted or predecessor mutated. No account/wallet key was touched.

Frozen Rust remains {frozen}; NGE_TARGET.json and the final Git tree checks confirm crates/ and programs/ are byte-identical. No shipped-file change triggered an ELF rebuild. These ELF pins are inherited, not rebuilt/reproduced here:

- Default f8c0ec72621fd5029a97d796c4a3623d0dc44a8e7074122372f9872915d143d4.
- Devnet 63ad3e9cc096dcbb55b3ca7ac7c8e89e6a845796ab5e4f5b7d15db96f3784299.
- Pool 121f3e29741f510e6dc42d0345fc3c36217600f0be337094855c4a9da2581548.

All stage commits are local with plain messages. The next deliverable is chain B's exact remaining auxiliary replay followed by a new combined audit and complete certificate check; no root or security target beyond the measured delta is claimed.
'''
(E/'NGE_HANDOFF.md').write_text(text)
print(json.dumps(dict(budget=budget,S_after=after,roots_closed=roots_closed)))
