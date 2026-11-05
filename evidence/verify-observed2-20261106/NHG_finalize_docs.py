from pathlib import Path
import json,re,subprocess,hashlib
E=Path(__file__).resolve().parent;R=E.parent.parent
result=json.loads((E/'NHG_FINAL_VALIDATION.json').read_text());export=json.loads((E/'NHG_EXPORT.json').read_text());paths=json.loads((E/'NHG_PATHS.json').read_text());retained=[paths[0],export['export_path']]+paths[1:];(E/'NHG_PATHS_RETAINED.json').write_text(json.dumps(retained,indent=1)+'\n')
open_rows=[]
for line in(E/'NHG_CONE.md').read_text().splitlines():
 m=re.match(r'\| (TX\d:\d+) \| OPEN \| (`[^`]+`) \| (.*) \|',line)
 if not m:continue
 row,name,reason=m.groups()
 if 'SLICE BOUNDARY' in reason:need='OWNER_BOUNDARY: not authorized to prove here; requires committed callee packet and caller-domain instance.'
 elif row=='TX1:129':need='LEAN/ASSOCIATION OPEN: native K077–080 support already exists; no additional Kani is automatically necessary. Need validated payload/decoder domain, full heap initialization/cleanup/emitted-body association. Final5 bounds/frame laws do not close it.'
 elif row=='TX1:130':need='LEAN/SOURCE-NONE OPEN: exact deployed no-observer/source certificate and coherent model instantiation; no Some/fn-pointer dependent Kani credit is permitted by quarantine.'
 elif row in ['TX1:133','TX1:134']:need='KANI + LEAN: actual parent state/error/array call-window association and SAME decoded polynomial/alpha/transcript domains; decoded payload147 carrier obligation remains, despite local row147 CLOSED.'
 elif row in ['TX1:136','TX1:137']:need='KANI + LEAN + OPEN CALLEES: no final native staged parent bridge or full packet/error/effect chain; must first close the named actual children. Root cannot follow from leaf counts.'
 else:need='KANI/COMPOSITION OPEN: a complete exact native/window/ABI and emitted-model/caller-domain association for this member is absent. Existing model-only/local evidence is not a composed row; resolve its named real open children first.'
 open_rows.append(dict(row=row,function=name.strip('`'),remaining=reason,required=need))
(E/'NHG_REMAINING.json').write_text(json.dumps(dict(budget_used=result['budget_used'],root137_closed=False,rows=open_rows,reason_for_stop='ALL stated proof budgets exhausted. This is not a Kani-only stop: remaining5 Lean/support slots were consumed by local domain/frame proof and final audits.'),indent=1)+'\n')
(E/'NHG_REMAINING.md').write_text('# Remaining cone obligations\n\nBudget exhausted:80 Kani,90 Lean/support,1 extraction.18 new NHG rows and11\ninherited NGX rows are admitted. Root137 and finish136 are OPEN.\n\nNative claims windows and the final five Lean bounds/frame laws are SUPPORT\nONLY. Some remaining claims/observer work is Lean/source association rather\nthan necessarily new Kani; it remains because the Lean budget is also fully\nconsumed. Every other member’s exact native/callee/boundary need is listed\nbelow. Uncommitted sibling work and out-of-slice proof work are not assumed.\n\n| Row | Function | Needed before admission | Exact obligation |\n|---|---|---|---|\n'+''.join(f"| {x['row']} | `{x['function']}` | {x['required']} | {x['remaining']} |\n"for x in open_rows))
audit=json.loads((E/'NHG_AUDIT.json').read_text());audit['final']=dict(status='PASS',joint='NHG_L088',raw='NHG_L089',final_support_raw_roots=5,total_NHG_roots=112,scan='NHG_L090',scan_modules=result['scan_modules'],standard_axioms=['propext','Classical.choice','Quot.sound'],new_rows_after_stage4=0,root137_closed=False,export='NHG_EXPORT.json',budget_used=result['budget_used']);(E/'NHG_AUDIT.json').write_text(json.dumps(audit,indent=1)+'\n')
with(E/'NHG_HANDOFF.md').open('a')as f:f.write(f'''

## FINAL — all budgets consumed

Proof budgets:80/80 Kani,90/90 Lean/support,1/1 extraction. Final joint L088,
raw L089 (five new support roots), NFX L090 all exit0.112 total NHG roots,
{result['scan_modules']} loaded modules, standard axioms only. Final scan peak7019012KiB,
swap0. `NHG_final_validate.py` PASS; final denial suite is additive.

18 NHG rows remain CLOSED; no row is added after stage4. Claims129, mark130,
round133, rounds134, finish136 and verify_observed137 remain OPEN. The final
five proofs establish decode29 byte ranges, row-copy value frame, payload
length and round widths; they DO NOT establish the private payload borrow
bridge or full claims initialization/heap/source association. See per-member
`NHG_REMAINING.json` / `.md` for exact needs and owner boundaries.

Retained export: `{export['export_path']}`.
{export['exported_bytes']} bytes, including the unchanged audit binaries;
{export['closure_objects']} resolved object hashes (including Aeneas) are pinned in
`NHG_FINAL_CLOSURE_PINS.json.xz` plus uncompressed SHA256. Cache was not deleted.
`NHG_PATHS_RETAINED.json` gives scratch-first then retained-export resolution.
To reuse the audit executables, use the retained `bin/` copies; the owned
scratch objects/native binaries and Cargo targets were removed only after
export hash verification. `NHG_CLEANUP.json` records paths/bytes and66.8GB free.
All borrowed caches and every sibling/live/session-A worktree remain untouched.

Export/cleanup were capped or small file-packaging IO with zero Lean/Rust/Kani/
extraction invocations; they consume no additional proof budget. Packaging
admission, transport, time and source are retained separately. No new native
or proof command may run under the exhausted budget.

Production source was not changed; no ELF rebuild trigger. Retained release
hashes remain default f8c0ec72621fd5029a97d796c4a3623d0dc44a8e7074122372f9872915d143d4,
devnet63ad3e9cc096dcbb55b3ca7ac7c8e89e6a845796ab5e4f5b7d15db96f3784299,
Pool121f3e29741f510e6dc42d0345fc3c36217600f0be337094855c4a9da2581548.
No trust row or100-bit PER-ATTEMPT/privacy/two-transaction requirement changed;
P6/D188 and Std interpretation are retained/reclassified, never removed.
No push.
''')
with(E/'NHG_STAGES.md').open('a')as f:f.write('\n\n## Final support stage\n\nL086 was an excluded local editing failure; corrected L087 proves five local\nclaims/round bounds and generic KMX row frame. Joint L088, raw5 L089 and\nNFX13559 L090 pass. No claims129 or parent/root promotion. All proof budgets\nconsumed; final export is file IO only, not a further prover invocation.\n')
with(E/'NHG_FAILING_STEP.md').open('a')as f:f.write('\n\nFinal missing steps: claims129 needs the SAME private validated-record payload/decoder domain and complete heap/emitted-body/cleanup frame; K077–080 and final5 local bounds are support only. Round133/rounds134 need caller domains and native parent frame. Mark130 needs the deployed-None source/model certificate without quarantined function-pointer credit. Finish136 additionally needs actual mask76/circle142->156/terminal dependencies and complete state/error/effects composition. Root137 needs finish and its own staged native/emitted association. No success premise is substituted.\n\nCorrected local Lean input failures are preserved in their own receipts: L004,L006,L012,L015,L034–036,L038,L040,L042–045,L053–054,L057–058,L068–069,L071,L073,L075,L077–078,L086. Failed imports, reserved identifiers, projection/let normalization and missing explicit coherent imports were corrected in the later selected targets. No failed candidate or sorryAx reaches a combined import. L017/L052 were local guard refusals before any SSH/scope and are conservatively charged support attempts.\n')
# Own change inventory and immutable inherited ELF hashes; no release rebuild claim.
changed=subprocess.check_output(['git','diff','--name-only','9cb318748ee^','--','crates','programs','docs/research/100bit-spend-path-20261013/crates','docs/research/100bit-spend-path-20261013/programs'],cwd=R,text=True);assert not changed
(E/'NHG_SHIPPED_SOURCE_CHECK.json').write_text(json.dumps(dict(reference='9cb318748ee^',changed_shipped_files=[],rebuild_required=False,verification='No task changes in shipped crates/programs; scratch cfg(kani) overlays only, frozen-source identity per every Kani receipt.',inherited_elf_hashes=['f8c0ec72621fd5029a97d796c4a3623d0dc44a8e7074122372f9872915d143d4','63ad3e9cc096dcbb55b3ca7ac7c8e89e6a845796ab5e4f5b7d15db96f3784299','121f3e29741f510e6dc42d0345fc3c36217600f0be337094855c4a9da2581548']),indent=1)+'\n')
print('Final handoff and per-member remaining obligations written')
