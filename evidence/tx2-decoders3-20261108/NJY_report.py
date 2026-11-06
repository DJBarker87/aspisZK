from pathlib import Path
import json,hashlib,subprocess,lzma
E=Path(__file__).resolve().parent
rs=[json.loads(l)for l in(E/'NJY_ATTEMPTS.jsonl').read_text().splitlines()];audit=json.loads((E/'NJY_AUDIT.json').read_text());assert audit['gate']=='PASS_LOCAL_PACKET_PENDING_NEXT_LEDGER_GATE'
export=json.loads((E/'NJY_EXPORT.json').read_text());validation=json.loads((E/'NJY_VALIDATION.json').read_text());assert not validation['errors']
resources=dict(kani=dict(numbered_slots=90,launched=89,timeout=['NJY_K041'],skipped=['NJY_K042'],limit=90),formal=dict(scopes=sum(r['kind']!='kani'for r in rs),limit=90,failures=[r['attempt']for r in rs if r['kind']!='kani'and r['exit_status']!=0]),extraction=dict(used=0,limit=1),wall_seconds=sum(r['wall_seconds']for r in rs),peak_rss_kib=max(int(r['peak_rss_kib'])for r in rs),swaps=0,scopes='serial; every admission exit0 AND allowed:true; MemoryHigh6G/Max8G/SwapMax0/Tasks64; Lean-M7000; optimized Rust',index=[{k:r[k]for k in ['attempt','kind','module','exit_status','wall_seconds','peak_rss_kib','swaps','source_revision','print_axioms']}for r in rs],export=export)
(E/'NJY_RESOURCE_INDEX.json').write_text(json.dumps(resources,indent=1)+'\n')
(E/'NJY_REMAINING.md').write_text('''# NJY remaining obligations

Target not yet established. Five local candidates are labelled CLOSED under (ah), pending the NEXT lead ledger gate. The authoritative NJW baseline stays484 CLOSED /0 QUALIFIED /115 OPEN of599. Proposed delta+5, prospective489/110 only after that gate; no parent is promoted.

|Member|Completed owned obligation|Remaining and why no further owned Lean attempt is needed|
|---|---|---|
|TX2:149 identity|Inherited actual full-Result contract/control and symbolic width guard; exact identity Result fidelity; complete hand reference=model and reversible canonical carrier; current roots and both combined audits pass|Lead gate admission. Internal helper of master, no independent adapter slot. No remaining owned model/domain/error/carrier lemma.|
|TX2:152 checkpoint|Complete source-order length/header/digest-window/digest-map/loop-window/update+error-frame/constructor contracts and controls; native ONE iteration plus Lean window/frame and NJQ induction; CLOSED digest146 instantiated internally; full canonical Result|Lead gate admission. Raw helper uses account-format errors. Box/ProgramError consumer op49 is a different wrapper outside this job (NJY-B1), never an added root assumption. No further owned Lean-only lemma remains.|
|TX2:153 master|Complete source-order guards and child windows/maps, arbitrary-prestate loop window/step/frame, full constructor/validator suffix; identity149 then CLOSED policy150/validator157 instantiated at SAME values; all Result arms/record fields|Lead co-admission with identity149. Box/ProgramError op48 wrapper remains outside this function list (NJY-B1); the raw helper bridge does not promote it. No remaining owned model, loop, child-domain or carrier lemma.|
|TX2:201 entry|All four source segments and paired controls; exact returned-record fidelity; CLOSED status192/validator206 instantiated internally; direct canonical slot32 installation and full Result|Lead gate admission. No free child-success, endpoint or dictionary premise. No owned Lean-only gap remains.|
|TX2:203 registry|All four source segments and paired controls, every record field/delay/error branch; exact returned-record fidelity; CLOSED validator208; direct canonical slot31 installation and full Result|Lead gate admission. No remaining owned Lean-only obligation.|

Native budget: all90 slots charged,89 actual launches, K042 skipped after K041 TIMEOUT. No further native scope may launch. K041 is retired with its exact source and replaced by genuinely smaller window/update contracts; no cap/timeout increase. Formal budget remains, but every owned reference/model, bounds, complete Result, child instantiation, induction, window/frame, canonical transport, slot installation and audit obligation has been attempted. New wrappers, different slices, headline joins or repeated green audits would be outside this job; they are not concealed as exhausted-budget blockers. Both allowed combined audits are used, the second justified by new NJY_Install source. Optional extraction was unnecessary under (ay)(2).

NJY-B1: L017 exposed that op48/49 return ProgramError and represent boxed decoder wrappers. Direct installation of the raw helper account-error functions was ill-typed and STOPPED. L018 installs31/32 only and preserves43/44 and48/49. Wrapper composition is the future owner's obligation, with no new trust row, altered carrier, success assumption or statement change. The next ledger must retain this boundary and all original U04 context. The 100-bit PER-ATTEMPT headline, privacy, two-transaction game and physical/source-to-ELF obligations remain unestablished as before.
''')
commits=subprocess.check_output(['git','log','--oneline','-4'],text=True).strip()
(E/'NJY_HANDOFF.md').write_text(f'''# NJY handoff

**Target not yet established. Five local candidates CLOSED under (ah), awaiting NEXT ledger gate.** Baseline NJW ledger16 remains484 CLOSED /0 QUALIFIED /115 OPEN of599. Proposed delta+5 only; no parent promoted. Branch codex/cx-tx2-decoders3-20261107; local commits, no push. Only NJY evidence/modules changed.

## Established and qualified

TX2:149 identity,152 checkpoint,153 master,201 entry,203 registry have complete source-ordered native/reference/model packets. (ay)(2) qualifies all five through retained NJQ E001; no re-extraction or unchanged timeout rerun. Identity reuses NJQ's actual144-byte full-Result contract/control and width guard. Other rows use (ay)(3) source segments with exact modifies and paired failures; all errors, child windows, records and early suffix stops are covered. Standard operations execute inside segments or use the reviewed ONE-step/finite-induction loop boundary, not free operations at roots. Current model proofs reuse NJQ's source/bounds/closed-child/error/carrier/induction work without duplicating it.

K041 broad checkpoint step timed out90s; no credit, K042 skipped. Factored window and update contracts K069-K074 pass, including write-before-rejection state. Root/model support and NJY_WindowStep compose full frame/induction. Fidelity controls cover all parent records and the intermediate word-array, step-post, binding-pair and digest Results. Exact KMX configuration, matched failures, offline frozen graph/lock before every run and unchanged lock after; all-crate features retained in receipts. No writable static, function-pointer-dependent credit, arithmetic product stub or quarantined/suspended harness.

ReviewedTranscription NJY-RT149/152/153/201/203 and native cut manifests extend P6/D188 option-A RECLASSIFICATION; no runtime or cryptographic trust row added or removed. Child146,150,157,192,206,208 laws are applied on SAME inputs; master co-admits identity149. Only reviewed native Cut hypotheses occur in positive roots; NJY_HYPOTHESES.json inventories printed statements. No arbitrary Ops, runtime Boolean, successful-child or endpoint-equality premise.

NJY-B1: L017 correctly rejected raw master/checkpoint functions at48/49: wrapper slots use Box/ProgramError, raw helpers account-format errors. That installation was STOPPED, not repaired with a carrier assumption. L018 installs direct registry31/entry32 only and preserves digest/error43/44 and wrapper48/49. The raw helper rows may be admitted; their wrapper consumers remain outside this job, with no parent closure claimed.

## Validation and retention

Focused current modules pass. Failed L006 bound proof and L007 rewrite proof were repaired under fresh source attempts L015/L016; their error-recovery sorryAx is excluded. L017 type failure is excluded; L018 current installation passes. Every new top theorem prints its statement/axioms; accepted axioms are a subset of propext/Classical.choice/Quot.sound.

Two and only two completed combined audits. Final L020 imports NJW+NJQ+NJY with AspisR1.RPx_Deployed.deployed. L021 same-binary eight ax2 fixtures; L022 raw ax2 on105 roots (all NJQ/new roots plus headline), standard axioms; baseline NJW9608-root audit reused with exact selected object pins. L023 NFX exit0 across{audit['NFX']['modules']} modules, zero dangling/conflicting owners/import mismatches. L024 pins selected closure, zero NJW predecessor mismatches. Full printed roots, cut definitions, receipts and SHA-indexed source inputs retained. NJY_CLOSED.json and NJY_LEDGER_DELTA.json are packets, not authoritative promotions.

Resource use:90/90 native slots (89 launches,1 skipped),{resources['formal']['scopes']}/90 formal/support scopes,0/1 extraction; total scope wall{resources['wall_seconds']:.3f}s; max peakRSS{resources['peak_rss_kib']}KiB, swap0. Every scope has allowed:true AND exit0 admission,6G high/8G max/Swap0/Tasks64; Lean-M7000, optimized Rust, one scope at a time. Exact target/argv/status/wall/RSS/swap/revision/source/dependency/Aeneas hashes and printed axioms are in NJY_ATTEMPTS.jsonl and per-scope receipts. No cap or timeout raised.

Own host workspace /home/dombarker/project-offloads/codex-cx-tx2-decoders3-20261107; own CARGO_TARGET_DIR there/NJY_target. Seeded NJQ FIRST6,020,032bytes, then NJW1,365,368bytes; every imported hash recorded. Private Rust seed24,810,888bytes, frozen lock5782e6a32026fdd95d252d0db7ea20b16716e6deb4f5a397e744886bb6ba22ef. Final export {export['export']}, {export['bytes']}bytes; retain caches and both export generations. No session-A/sibling worktree changed. No wallet/key/fund action. No objects/binaries/ELFs or file over20MB committed; all evidence inputs retained by SHA, pycache removed before commits.

Frozen source4bb3b3f51e16b4525f1d10336e2b0bcbbd775387 unchanged in research crates/programs; only private cfg(kani) harness/trait additions erase exactly. No ELF rebuild trigger. Inherited pins, NOT rebuilt/reverified here: default f8c0ec72621fd5029a97d796c4a3623d0dc44a8e7074122372f9872915d143d4; devnet63ad3e9cc096dcbb55b3ca7ac7c8e89e6a845796ab5e4f5b7d15db96f3784299; Pool121f3e29741f510e6dc42d0345fc3c36217600f0be337094855c4a9da2581548. Frozen3/deployed headline, L154 statement parameter, narrowed D188,100-bit PER-ATTEMPT/privacy/two transactions unchanged. No headline hypothesis discharged. Next deliverable: lead gate on these five raw-body packets, retaining NJY-B1 and parent physical/wrapper obligations. NJY_REMAINING.md gives member-by-member scope/budget reasons.

Pre-final stage commits:\n\n{commits}\n
Final packet commit follows; no push.
''')
print(json.dumps(dict(candidates=5,formal_scopes=resources['formal']['scopes'],native_slots=90,target='NOT_YET_ESTABLISHED')))
