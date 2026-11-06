from pathlib import Path
import json,lzma,hashlib,subprocess
E=Path(__file__).parent
rs=json.loads(lzma.open(E/'NJA_TARGET_ROWS.json.xz').read())
raw=json.dumps(rs,indent=2).encode();(E/'NJA_TARGET_ROWS.json.sha256').write_text(hashlib.sha256(raw).hexdigest()+'\n')
allrows=json.loads(lzma.open('evidence/ledger13-20261107/NIU_LEDGER.json.xz').read())['rows'];statuses={r['function']:r['status'] for r in allrows}
text=['# NJA scope — stage 0','', 'Target not yet established. Baseline NIU: 432 CLOSED / 0 QUALIFIED / 167 OPEN; all 28 assigned occurrences remain OPEN. Full original row records, frozen body hashes, discovery evidence, and caller clauses are retained without omission in NJA_TARGET_ROWS.json.xz. No inventory evidence receives proof credit.','', '## Model owners and domains','', 'Multiproof: adopted binary cohort MultiproofConeRef.reference, consumed by MultiproofConeP6Frozen2Stage.sourceBatch / sequence and MultiproofConeP6Callbacks. Source scalar helpers have inlined consumers rather than named cohort helpers; exact association must be proved, not inferred from names. The eight-way-only value_at has no reached binary consumer (NDT rejection); unresolved domain/reachability finding. Poseidon: adopted AspisR1Stage2.aspis_statement.poseidon2 emission; exact selected object owner and trace function association remain to pin before credit. Do not substitute state_only_poseidon (QM31) for this M31 module.','', 'TX1/TX2 non-generic multiproof functions have identical frozen bodies and signatures. Digest parents/verify_in_place share generic source but require deployed SolanaDigest instance pinning before claiming identical monomorphization. Per-occurrence obligations differ: TX1 <=10 entries; TX2 <=12, same 16-cell buffers. Every occurrence remains separately checked.','']
for r in rs:
 text += ['## '+r['row']+' '+r['function'],'', 'Frozen body SHA256: `'+r['frozen_body_sha256']+'`. Obligation hash: `'+r['obligation_statement_hash']+'`.','', 'Model: '+('MultiproofConeRef.reference binary inlined consumer; association OPEN.' if '/multiproof.rs' in r['function'] else 'AspisR1Stage2.aspis_statement.poseidon2 corresponding emitted body; selected owner OPEN.'),'', 'Inventory domain: '+ '; '.join(x['domain'] for x in r['obligation']['inventory_domain_obligations']),'', 'Callees: '+ ('; '.join(c+' ['+statuses.get(c,'not inventoried')+']' for c in r['canonical_callees']) or 'none')+'.','', 'Caller obligations: '+str(len(r['obligation']['caller_domain_obligations']))+'; exact clauses retained in the row snapshot. No clause discharged.','']
(E/'NJA_SCOPE.md').write_text('\n'.join(text))
(E/'NJA_HANDOFF.md').write_text('''# NJA early handoff

Target not yet established. Branch codex/cx-multiproof-20261107; no push.
Stage 0 pins all 28 NIU obligations in NJA_TARGET_ROWS.json.xz; NJA_SCOPE.md lists domains and dependencies. No native, Lean or composed closure yet. Budget 0/120 Kani, 0/100 Lean, 0/1 extraction. Next: additive whole-module extraction selector, admitted preflight, one extraction; then bottom-up emitted/cohort equations and native local-record controls. All code and evidence owned by NJA only; frozen shipped sources unchanged.

Host: dombarker@100.108.41.90. Own workspace /home/dombarker/project-offloads/codex-cx-multiproof-20261107. Own CARGO_TARGET_DIR there/NJA_target. Retained cache is never deleted. NIU export is first seed; SInt2 objects are reused. Each run requires exit0 and allowed:true; caps 6G/8G/swap0/tasks64, Lean -M7000. No launches yet. Host read-only disk observation: 98%, 41G available; avoid corpus duplication.

Retained trust: frozen3 / RPx_Deployed.deployed, L154 parameter, narrowed D188/P6 option A, existing runtime/SDK/std/allocator/source-to-ELF boundaries. No trust added or removed. value_at binary reachability unresolved. No live session-A or sibling worktree accessed. No key operations.
''')
(E/'NJA_ATTEMPTS.jsonl').touch()
print('NJA stage 0: 28 full obligations pinned; no closure claimed')
