#!/usr/bin/env python3
"""PCWA_hand_models.py: write PCWA_HAND_MODELS.json (lead addendum): every external name (type or function) of a fresh emission that
resolves, in the equality statements, to a gate hand-written model rather than an Aeneas external/opaque declaration, plus the gate-side
hand edits that change a declaration relative to the raw emission. RECORD ONLY: no trust row is added or proposed.
Per entry: gate module, external name, gate definition (file + exact text), fresh form, pinned crate+version, dependent reached definitions."""
import json,re,subprocess
from pathlib import Path
E=Path(__file__).resolve().parent
def git(p): return subprocess.check_output(['git','-C',str(E.parent.parent),'show','research:'+p]).decode()
KW=r'(?:def|abbrev|axiom|opaque|instance|theorem|class|structure|inductive|noncomputable def)'
def decl(text,name):
    lines=text.split('\n');out=[]
    for i,l in enumerate(lines):
        if re.match(r'\s*(@\[[^\]]*\]\s*)?(local\s+)?(noncomputable\s+)?'+KW+r'\s+(@?\[?[^ ]*\]?\s*)?'+re.escape(name)+r'(\s|$|:)',l) or (re.match(r'\s*(@\[[^\]]*\]\s*)?(local\s+)?'+KW+r'\b',l) and re.search(r'(^|[\s.])'+re.escape(name)+r'(\s|$|:)',l.split(':=')[0])):
            j=i
            while j>0 and (lines[j-1].strip().startswith('--') or lines[j-1].strip().startswith('/--') or lines[j-1].strip().startswith('Source:') or lines[j-1].strip().startswith('Name pattern') or lines[j-1].strip().startswith('Visibility') or lines[j-1].strip().endswith('-/')):j-=1
            k=i+1
            while k<len(lines) and not (re.match(r'(@\[|/--|def |abbrev |axiom |opaque |instance |theorem |class |structure |inductive |namespace |end |noncomputable )',lines[k])): k+=1
            return '\n'.join(lines[j:k]).rstrip()
    return None
def fresh_decl(path,name):
    return decl((E/path).read_text(),name)
def mentions(fresh_funs,name):
    t=(E/fresh_funs).read_text();blocks=re.split(r'\n(?=/-- \[)',t);res=[]
    for b in blocks:
        m=re.search(r'\n(?:@\[[^\]]*\]\n)?(?:noncomputable )?(?:def|abbrev|structure|inductive|instance|opaque|axiom)\s+(\S+)',b)
        if m and re.search(r'(?<![\w.])'+re.escape(name)+r'(?![\w])',b.split('\n',1)[1] if '\n' in b else b) : res.append(m.group(1))
    return sorted(set(res))
GITFILES={
 'NHI_FilledExternal':'evidence/slice-d-pair-20261106/NHI_FilledExternal.lean',
 'FIo_NativeExternal':'evidence/replay-dry8-20261026/RPz7_FIo_NativeExternal.lean',
 'FIo_NativeTypes':'evidence/replay-dry8-20261026/RPz7_FIo_NativeTypes.lean',
 'NHJ_FunsExternal':'evidence/slice-d-entry3-20261106/NHJ_SnapshotReference.FunsExternal.lean',
 'NHJ_Types':'evidence/slice-d-entry3-20261106/NHJ_SnapshotReference.Types.lean',
 'NEI_FunsExternal':'evidence/slice-q-mul2-20261101/NEI_PushRaw/FunsExternal.lean',
 'NEV_FunsExternal':'evidence/slice-q-mul3-20261103/NEV_AccumulateRaw/FunsExternal.lean',
 'NFS_AccumPart00':'evidence/slice-q-accum-20261104/NFS_AccumPart00.lean',
 'NEV_Types':'evidence/slice-q-mul3-20261103/NEV_AccumulateRaw/Types.lean',
 'WAdm_FunsExternal':'evidence/replay-dry8-20261026/RPz7_WAdm_Fissioned_FunsExternal.lean',
 'WAdm_TypesExternal':'evidence/replay-dry8-20261026/RPz7_WAdm_Fissioned_TypesExternal.lean',
 'WAdm_Types':'evidence/replay-dry8-20261026/RPz7_WAdm_Fissioned_Types.lean',
 'NGD_Types':'evidence/slice-d-parser-20261104/NGD_AtG/Types.lean',
 'S8_Funs':'docs/research/100bit-spend-path-20261013/lean/S8OwnedP6/Funs.lean',
 'S8_Types':'docs/research/100bit-spend-path-20261013/lean/S8OwnedP6/Types.lean',
}
G={k:git(v) for k,v in GITFILES.items()}
entries=[]
def add(**k): entries.append(k)
STD='Rust std (core/alloc) at the nightly-2026-09-17 sysroot of the pinned Charon; not a crates.io package'
CORE='aspis-core 0.1.0 (frozen path crate, workspace revision 4bb3b3f51e16b4525f1d10336e2b0bcbbd775387)'
def ext(module,fresh_dir,fresh_funs,tmpl,gate_key,gate_file_key,crate,extra_gate_keys=()):
    t=(E/fresh_dir/tmpl).read_text()
    names=[]
    for l in t.split('\n'):
        m=re.match(r'axiom\s+(\S+)',l)
        if m: names.append(m.group(1))
    out=[]
    for n in names:
        gt=None;gf=None
        for key in (gate_key,)+tuple(extra_gate_keys):
            gt=decl(G[key],n)
            if gt: gf=GITFILES[key];break
        out.append(dict(gate_module=module,external_name=n,kind='function' if 'Types' not in tmpl else 'type',
          gate_definition=dict(file=gf,text=gt) if gt else dict(file=None,text=None,note='no top-level declaration with this exact name found by the extractor; the name resolves through an alias or an inherited namespace of the gate file (see gate_file)',gate_file=GITFILES[gate_file_key]),
          fresh_form=dict(file=f'{fresh_dir}/{tmpl}',text=fresh_decl(f'{fresh_dir}/{tmpl}',n)),pinned_crate=crate,dependent_reached_definitions=mentions(f'{fresh_dir}/Funs.lean',n)))
    return out
# NHI_FilledExtracted
ents=ext('NHI_FilledExtracted','PCWA_E004_emitted/raw/NHI_FilledRef','x','FunsExternal_Template.lean','NHI_FilledExternal','NHI_FilledExternal',STD)
for e in ents:
    n=e['external_name'];e['gate_definition']=dict(file=GITFILES['NHI_FilledExternal'],text=decl(G['NHI_FilledExternal'],n),resolves_to=dict(file=GITFILES['FIo_NativeExternal'],text=decl(G['FIo_NativeExternal'],n)))
entries+=ents
e=ext('NHI_FilledTypes','PCWA_E004_emitted/raw/NHI_FilledRef','x','TypesExternal_Template.lean','NHI_FilledExternal','NHI_FilledExternal',STD)
for x in e: x['gate_definition']=dict(file=GITFILES['NHI_FilledExternal'],text=decl(G['NHI_FilledExternal'],x['external_name']),resolves_to=dict(file=GITFILES['FIo_NativeTypes'],text=decl(G['FIo_NativeTypes'],x['external_name'])))
entries+=e
add(gate_module='NHI_FilledExtracted',external_name='FIo_Native.Allocation (instance-implicit parameter)',kind='type class / hand-added binder',
    gate_definition=dict(file='evidence/slice-d-pair-20261106/NHI_FilledExtracted.lean',text='variable [allocation : FIo_Native.Allocation]',resolves_to=dict(file=GITFILES['FIo_NativeExternal'],text=decl(G['FIo_NativeExternal'],'Allocation'))),
    fresh_form=dict(file=None,text='(absent: the raw emission has the axiom alloc.vec.Vec.try_reserve_exact and no allocator binder)'),pinned_crate=STD,dependent_reached_definitions=['filled_ref','filled_ref.closure.Insts.CoreOpsFunctionFnOnceTupleTryReserveErrorError.call_once'],
    note='Equality statements copy this binder verbatim as --fresh-prelude (gate_sources/NHI_FilledExtracted.prelude.lean); theorem holds for every instance.')
# NHJ
entries+=ext('NHJ_SnapshotReference.Funs','PCWA_E003_emitted/raw/NHJ_SnapshotReference','x','FunsExternal_Template.lean','NHJ_FunsExternal','NHJ_FunsExternal','Rust std alloc::string::String::clone, nightly-2026-09-17 sysroot')
add(gate_module='NHJ_SnapshotReference.Types',external_name='ProgramError (type, replaced by alias)',kind='type alias replacing an emitted inductive',
    gate_definition=dict(file=GITFILES['NHJ_Types'],text=decl(G['NHJ_Types'],'ProgramError')),
    fresh_form=dict(file='PCWA_E003_emitted/raw/NHJ_SnapshotReference/Types.lean',text=fresh_decl('PCWA_E003_emitted/raw/NHJ_SnapshotReference/Types.lean','ProgramError')),
    pinned_crate='nhj_snapshot_reference 0.1.0 (reference crate, source sha256 e8a85ac9...); alias target NGL_MetaReference.ProgramError (ngl_reference crate)',
    dependent_reached_definitions=['ProgramError.Insts.CoreCloneClone.clone','snapshot_ref'],note='Both dependent equalities remain commented obligations (transport-needed): constructors are not reachable through the gate alias.')
# NGD
add(gate_module='NGD_AtG.Types',external_name='import_union_discriminant (registration attribute) / ImportUnionNamedDiscriminant',kind='hand-edited attribute and import',
    gate_definition=dict(file=GITFILES['NGD_Types'],text='\n'.join(l for l in G['NGD_Types'].split('\n') if 'import_union_discriminant' in l or 'ImportUnionNamedDiscriminant' in l)),
    fresh_form=dict(file='PCWA_E002_emitted/raw/NGD_AtG/Types.lean',text='@[discriminant isize]   (Aeneas registration attribute on inductive Error)'),
    pinned_crate='nfu_reference 0.1.0 (reference crate, source sha256 a4cf8bb1...)',dependent_reached_definitions=['Error'],note='Discriminant-reading instance is produced by a different attribute in the gate; the Error constructors are text-identical after stripping registration attributes; no Lean proof of the inductive identity is generated (types are text-identical-only).')
# NEI_PushRaw
entries+=ext('NEI_PushRaw.Funs','PCWA_E009_emitted/raw/NEG_PushActual','x','FunsExternal_Template.lean','NEI_FunsExternal','NEI_FunsExternal',STD+'; aspis-core field types per frozen tree')
# NEV / NFS
fe=ext('NEV_AccumulateRaw.Types / NFS_AccumPart00','PCWA_E010_emitted/raw/NEI_AccumulateIsolated','x','FunsExternal_Template.lean','NFS_AccumPart00','NFS_AccumPart00',CORE+'; trace module of aspis-r1-cost-probe; BatchedWeights::push of the same isolated crate',('NEV_FunsExternal',))
entries+=fe
add(gate_module='NEV_AccumulateRaw.Types',external_name='transport.Variant discriminant instance (NEV_discriminantVariant)',kind='hand-added instance replacing @[discriminant isize]',
    gate_definition=dict(file=GITFILES['NEV_Types'],text='\n'.join(G['NEV_Types'].split('\n')[72:80])),fresh_form=dict(file='PCWA_E010_emitted/raw/NEI_AccumulateIsolated/Types.lean',text='@[discriminant isize] on inductive transport.Variant'),
    pinned_crate='aspis-r1-cost-probe transport::Variant (isolated copy, frozen tree)',dependent_reached_definitions=['Prepared'],note='Gate comment: instance-name repair only.')
# WAdm
entries+=ext('RPz7_WAdm_Fissioned_Funs','PCWA_E011_emitted/raw/WAdm_Fissioned','x','FunsExternal_Template.lean','WAdm_FunsExternal','WAdm_FunsExternal','wadm_native_fixture (cut crate); core/alloc std from the original toolchain')
entries+=ext('RPz7_WAdm_Fissioned_Types','PCWA_E011_emitted/raw/WAdm_Fissioned','x','TypesExternal_Template.lean','WAdm_TypesExternal','WAdm_TypesExternal','Rust core::array::IntoIter')
for tn in ['aspis_core.field.M31','aspis_core.field.CM31','aspis_core.field.QM31','aspis_core.circle.SecureCirclePoint','aspis_core.field.wide_exact.WideExact','aspis_core.digest.Digest32','aspis_r1_cost_probe.transport.Variant','aspis_r1_cost_probe.verifier.Prepared']:
    add(gate_module='RPz7_WAdm_Fissioned_Types',external_name=tn,kind='type alias replacing an emitted native type',gate_definition=dict(file=GITFILES['WAdm_Types'],text=decl(G['WAdm_Types'],tn)),
        fresh_form=dict(file='PCWA_E011_emitted/raw/WAdm_Fissioned/Types.lean',text=fresh_decl('PCWA_E011_emitted/raw/WAdm_Fissioned/Types.lean',tn)),pinned_crate=CORE+'; aliases target OraclePortCkptAbi2Extracted / AspisR1Stage2 extractions',
        dependent_reached_definitions=mentions('PCWA_E011_emitted/raw/WAdm_Fissioned/Funs.lean',tn)[:30],note='All 24 Funs equalities close by rfl against these aliases; the alias targets are other gate modules whose own provenance is a separate obligation (nominal alias, not an equality of structure texts).')
# S8
s8t=[l for l in G['S8_Funs'].split('\n')][16:22]
add(gate_module='S8OwnedP6.Funs',external_name='Discriminant (Option T) Isize (local instance optionDiscriminant)',kind='hand-added local instance',gate_definition=dict(file=GITFILES['S8_Funs'],text='\n'.join(s8t).strip()),
    fresh_form=dict(file=None,text='(absent in the raw emission extraction-complete/generated/S8OwnedP6/Funs.lean)'),pinned_crate=STD+' (core::option::Option residual); tools/s8-kani-20261021 crate',
    dependent_reached_definitions=['core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionInfallible.from_residual','aspis_core.field.CM31.from_le_bytes','aspis_core.field.QM31.from_le_bytes','check_values_owned_loop.body','check_values_owned_loop','check_values_owned'],
    note='Equality statements copy the instance verbatim as --fresh-prelude (gate_sources/S8OwnedP6.Funs.prelude.lean). Without it the fresh declarations do not elaborate (PCWA_L008).')
add(gate_module='S8OwnedP6.Types',external_name='Types.lean adaptation (ImportUnionNamedDiscriminant)',kind='hand-edited import/attribute',gate_definition=dict(file=GITFILES['S8_Types'],text='\n'.join(l for l in G['S8_Types'].split('\n') if 'ImportUnionNamedDiscriminant' in l or 'import_union_discriminant' in l)),
    fresh_form=dict(file='PCWA_E012_emitted/raw/S8OwnedP6/Types.lean',text='raw emission with @[discriminant isize]'),pinned_crate='tools/s8-kani-20261021 (s8-owned-correspondence 0.1.0)',dependent_reached_definitions=[])
json.dump(dict(schema='PCWA_HAND_MODELS v1',target_established=False,note='Record only (lead addendum 2026-11-09). No trust row is added, removed or proposed. Entries with gate_definition.text null need manual lookup; see PCWA_CLASSIFICATIONS.json HM-1.',entries=entries),open(E/'PCWA_HAND_MODELS.json','w'),indent=1)
print(len(entries),'entries;',sum(1 for e in entries if e['gate_definition'].get('text') is None),'without extracted gate text')
