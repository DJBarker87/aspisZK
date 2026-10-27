from pathlib import Path
import json,hashlib,collections
E=Path(__file__).resolve().parent
load=lambda n:json.loads((E/n).read_text())
surfaces=load('L8a_surface.json');structures=load('L8a_structure.json');roots=load('L8a_root.json')
assert len(surfaces)==len({x['name'] for x in surfaces})==9224
assert len(structures)==4909
assert [set(x['uncached_axioms']) for x in roots]==[{'propext','Classical.choice','Quot.sound'}]*2
assert len([d for d in surfaces if d['axiom']])==108
assert all(not any(d['reachable_roots']) for d in surfaces if d['axiom'] and d['name'] not in {'propext','Classical.choice','Quot.sound'})
contract=Path('docs/research/100bit-spend-path-20261013/design/SECURITY-CONTRACT-20261021.md').read_text()
items={
'AspisR1.S2Trust.S2TrustedSdkBorrow':('S2TrustedSdkBorrow','C3-BIN 2026-10-23 01:20; LOG D189','accepted fifteen-field SDK/RefCell interpretation; no caller result'),
'AspisR1.S2W_TrustedStd.TrustedStd':('TrustedStd','LOG D157; C3-BIN 2026-10-23 18:05','slice copy only; W1 total abstract-domain versus valid native references remains'),
'AspisR1.Port1_Library.TrustedStd':('TrustedStd','same std ruling','pure Option/Result interpretation; deployment library item, not fresh top proof dependency'),
'AspisR1.S2W_DigestExtraction.AeneasExtraction':('AeneasExtraction','LOG D188; C3-BIN 2026-10-26 native Vec/Box ruling','source extraction association; not SBF equivalence; provenance finding D188-P below'),
'AspisR1.S2W_ExtractionBoundary.AeneasExtraction':('AeneasExtraction','LOG D188; S2W_DigestExtraction.sourceBoundary','older three-field derived interface, not independent additional trust'),
'AspisR1.S2W_D189Wrappers.Allocator':('Allocator','C3-BIN 2026-10-23 02:40/18:05','data-only allocate/cleanup interface; no success or account-access proposition'),
'AspisR1.AdapterRw.RuntimeEntrypointAdmission':('RuntimeEntrypointAdmission','C3-BIN 2026-10-23 02:40/18:05; LOG D189','initial heap validity/alias/counter facts only'),
'AspisR1.S2W_D189Consolidation.RuntimeEntrypointAdmission':('RuntimeEntrypointAdmission','same runtime admission + LOG D189','wrapper entry and related; nested entry fields are listed separately'),
'AspisR1.S2W_ExtractionBoundary.P1':('P1','existing P1; C3-BIN 2026-10-23 11:05/18:05','ideal-oracle realization, not a proof that SHA is random'),
'AspisR1.S2W_ExtractionBoundary.RuntimeSyscall':('RuntimeSyscall','existing P3; C3-BIN 2026-10-23 11:05/18:05','successful hash return only; no termination/totality premise'),
'AspisR1.S2X.CheckpointVersionBinding':('historical checkpoint interface','TRUST-AUDIT historical-interface row','not a new adopted top-level trust item; replaced by data persistence + game + source proofs'),
'AspisR1.S2W_AuthenticatedInputs.CheckpointVersionBinding':('historical checkpoint interface','same historical history interface','history wrapper, not a second runtime trust item')}
assert {d['name'] for d in structures if d['named_trust_record']}==set(items)
rows=[]
for d in structures:
 if not d['named_trust_record']:continue
 item,cite,scope=items[d['name']]
 for f in d['fields']:
  rows.append(dict(field=f['name'],record=d['name'],item=item,contract_literal_name_present=item in contract,acceptance=cite,scope=scope,import_roots=d['import_roots'],record_reachable_roots=d['reachable_roots']))
# TwoTransactionLaw is a definition, not a structure. No phantom structure field.
(E/'L8a_TrustFieldMap.json').write_text(json.dumps(rows,indent=2)+'\n')
standard={'propext','Classical.choice','Quot.sound'}
axioms=sorted((d for d in surfaces if d['axiom']),key=lambda d:d['name'])
lib=('Init','Lean','Std','Mathlib','Aeneas','AeneasMeta','Aesop','Batteries','Qq','ProofWidgets','ImportGraph','LeanSearchClient','Plausible')
classification=[]
for d in surfaces:
 if d['axiom']:
  group='standard axiom' if d['name'] in standard else 'F-AXIOM: uncontracted import-only axiom'
 elif any(d['owner']==x or d['owner'].startswith(x+'.') for x in lib):group='pinned toolchain/library implementation surface (P7 / D188 base)'
 else:group='repository implementation surface; unreachable in both kernel dependency traversals'
 classification.append(dict(name=d['name'],classification=group,import_roots=d['import_roots'],reachable_roots=d['reachable_roots']))
assert all(not any(d['reachable_roots']) for d in classification if d['classification'].startswith('repository'))
(E/'L8a_SurfaceClassification.json').write_text(json.dumps(classification,indent=2)+'\n')
md='''# Fresh Rc10 and ARX trust audit

**Kernel dependency audit passes; L188 release audit remains open with the findings below. The 100-bit deployed target is not established.** ARX remains a candidate, not an adopted replacement.

## Scope and evidence

`L8a_AuditRoot.lean` imports the fresh `RPz8_Rc10_Top` and `RPz8_ARX_Root`. Clean receipt L8a_006 prints exactly `[propext, Classical.choice, Quot.sound]` for both deployed theorems. L8a_007 independently walks checked kernel types, values (including opaque values), and inductive constructors without using cached axiom summaries. It then enumerates every checked constant in each root's actual transitive module import closure. The separate `import_roots` and `reachable_roots` columns below are ordered **Rc10, ARX**. Query-only `import Lean` additions are excluded by reconstructing each target's module graph from `EnvironmentHeader.moduleData.imports`, rather than taking the whole query environment.

The union contains 630,972 constants, 9,224 distinct declaration surfaces, and 4,909 structures. These are declaration counts, not premises or independent trust assumptions. Complete field inventories (including non-trust structures) are in `L8a_structure.json`; exact kernel types for trust fields are retained there and in L8a_007/stdout.log. All named trust records and definitions are printed freshly at L8a_008. `L8a_TrustFieldMap.json` maps each named trust field exactly once to its item and acceptance source.

| Root | Imported modules including libraries | Reachable kernel constants | Uncached axiom-info nodes |
|---|---:|---:|---|
'''
for r in roots:md+=f"| `{r['root']}` | {len(r['modules'])} | {r['reachable_count']} | `{', '.join(sorted(r['uncached_axioms']))}` |\n"
md+='''
The inherited RPz8 repository replay counts are 4,963 repository modules for Rc10 and 5,259 for ARX (union 5,260). Library modules are release-pinned trusted-base reuse, not fresh repository replay credit. The exact selected roots, producer objects, ordered LEAN_PATH, and Formatter hash are `L8a_HostPins.json`. Formatter is `63b8efa3940faa81bb26f1b6ea140b2d6b81c1f1155b3fafa0544f6e1e82b9fc`, 237,376 bytes, unchanged from RPz8.

## Findings and reconciliation

**F-AXIOM — closure-wide standard-only is false.** There are 108 imported axiom-info declarations: three standard and 105 other names. All 105 are unreachable in both top kernel traversals. Of those 105, 84 are the native formatter axioms classified by RPz8. The other 21 are explicitly listed in the complete axiom table below: Lean runtime/native/compiler infrastructure and Aeneas opaque model/test declarations. No imported axiom is silently treated as an approved security premise. `sorryAx` is present in Init, unreachable; this is not an observation of a proof using sorry. The 180 formatter implementation records in RPz8 remain unreachable; this audit's 84-name intersection agrees exactly. `Aeneas.Std.core.fmt.Formatter` is a reachable pure Unit definition, not an axiom. Kernel reachability clears the headline-use concern, but does not make the imported all-declaration gate true.

**F-CONTRACT — the binding contract lacks a complete explicit trust inventory.** Its owner amendment explicitly names `RuntimePersistence` / `CPR_DataPersistence.TwoTransactionLaw`, and names `RuntimeEntrypointAdmission`, `RuntimeSyscall`, and `Allocator` as existing items. It does not literally enumerate `S2TrustedSdkBorrow`, `TrustedStd`, `AeneasExtraction`, P6/Kani association, P7, or P1 by those names. Those have acceptance evidence in C3-BIN/LOG and TRUST-AUDIT, recorded below, but that is not a one-to-one named list inside SECURITY-CONTRACT. This is a documentation-reconciliation finding, not a claim the prior rulings were unauthorised and not permission to adopt extra trust. No contract or ledger is edited.

**W1 retained.** `S2W_TrustedStd.TrustedStd.slice_copy_from_slice` quantifies all abstract states/payloads; native interpretation was approved for valid borrowed references. A total abstract extension may be legitimate, but validity at each actual application must remain justified. This audit does not discharge or widen that association.

**D188-P retained.** The selected PublicPreparation producer is an adapted union, not byte-identical raw output of a certified extraction of the release pin. See `L8a_ProducerProvenance.md` and `L8a_ProducerComparison.json`; the current objects also differ from the historical e1d3e2db/06348080 object hashes, as expected after fresh compilation. Hashes are not interchanged between source and object identities.

Every opaque/partial/extern/implemented_by declaration is listed below with exact owner and reachability. These flags alone do not make a new mathematical axiom: opaque values are followed, safe logical definitions remain checked, and compiler-generated `_unsafe_rec` implementations are distinct from their proved logical definitions. All repository implementation surfaces in this inventory are unreachable from both tops; reachable implementation surfaces belong to the pinned Lean/Mathlib/Aeneas library base. `L8a_SurfaceClassification.json` records a classification for every row. The strict import-only axiom findings remain findings even when unreachable; there is no blanket promotion of external templates or unsafe code into D188.

## Named trust field reconciliation

Field rows preserve quantifiers and shared witnesses in their full raw kernel types; this table only indexes them. Reachability of a record is not evidence it is a free top premise (it may occur through a derived interface or conclusion). Old checkpoint-version interfaces are not counted as new adopted runtime items.

| Exact structure projection | Named item | Acceptance / scope | Literal item in contract? |
|---|---|---|---|
'''
for r in sorted(rows,key=lambda x:x['field']):md+=f"| `{r['field']}` | {r['item']} | {r['acceptance']}; {r['scope']} | {'yes' if r['contract_literal_name_present'] else 'no'} |\n"
md+='''
`AspisR1.CPR_DataPersistence.TwoTransactionLaw` is a definition, not a structure with fields. Its exact universal law and `visible` are freshly printed in L8a_008: adjacent ordinary-key loads see tentative data after successful parent status, starting data otherwise; zero lamports means absent. It matches owner amendment §3, data only. `CPR_Persistence.TwoTransactionLaw` is the older full-image candidate, explicitly unadopted; no stronger full-account persistence item is inferred.

P6/Kani association and P7 are external deployment/tool associations, not named Lean structure fields. The allocator is a data interface, not a successful-allocation axiom. P1 ideal-oracle realization remains distinct from cryptographic randomness assumptions. Query limits and approved game fields a–d are G conditions, not external trust. Child/source joins and native unsafe-memory/P6 correspondence remain proof obligations; they are not renamed trust. The old TRUST-AUDIT 83T expansion (34 SDK + 1 copy + 42 initial admission + 3 extraction + P1 + syscall + persistence) is an inherited ledger count, not a new absolute recount of candidate ARX.

## Complete axiom declaration list

| Exact name | Owning module | Imported Rc10/ARX | Reachable Rc10/ARX |
|---|---|---|---|
'''
fmt=lambda bs:'/'.join('yes' if b else 'no' for b in bs)
for d in axioms:md+=f"| `{d['name']}` | `{d['owner']}` | {fmt(d['import_roots'])} | {fmt(d['reachable_roots'])} |\n"
md+='''
## Complete implementation-surface declaration list

All rows with at least one of opaque, implemented_by, extern, partial are included exactly once. `implemented_by` gives the actual target; extern records attribute presence. Raw constant types are in L8a_007/stdout.log. This includes library/metaprogram implementation declarations: they are not silently excluded from closure membership.

| Exact name | Owning module | Flags / implemented_by target | Imported Rc10/ARX | Reachable Rc10/ARX |
|---|---|---|---|---|
'''
for d in sorted(surfaces,key=lambda x:x['name']):
 flags=[k for k in ['opaque','extern','partial'] if d[k]]
 if d['implemented_by']:flags.append('implemented_by `'+d['implemented_by']+'`')
 if not flags:continue
 md+=f"| `{d['name']}` | `{d['owner']}` | {', '.join(flags)} | {fmt(d['import_roots'])} | {fmt(d['reachable_roots'])} |\n"
(E/'L8a_TrustAudit.md').write_text(md)
print('audit report generated:',len(rows),'trust fields;',len(axioms),'axioms;',len(md),'bytes')
