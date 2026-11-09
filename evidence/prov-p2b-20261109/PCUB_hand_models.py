#!/usr/bin/env python3
"""PCUB_hand_models.py: PCUB_HAND_MODELS.json (record only, no trust row proposed) and PCUB_PROVENANCE.json (per-module transformation record).
Run from this directory after PCUB_final.py."""
import json, re, sys, glob, os, hashlib
from pathlib import Path
sys.path.insert(0, '.')
import PCUB_gen_equalities as G
EV = Path('..').resolve()
P = json.load(open('PCUB_PARTITION.json'))['modules']
ST = json.load(open('PCUB_EQ_STATUS.json'))
GS = json.load(open('inputs/gate_sources.json'))
CL = sorted(n for n in P if n.startswith('RPu') or n.startswith('RPv'))
TOOLCHAIN = 'nightly-2026-09-17 (rustc of the Charon/Aeneas stager, PCQC_E0nn_PINS.json environment); core/std items are not versioned by Cargo.lock'
dirs = []
for r in ['PCQ_E037', 'PCQ_E038', 'PCQ_E039', 'PCQ_E040']: dirs += glob.glob(f'{EV}/prov-p1a-20261109/{r}_emitted/raw/*')
for n in list(range(1, 13)) + [22, 23]: dirs += glob.glob(f'{EV}/prov-p1c-20261109/PCQC_E{n:03d}_emitted/raw/*')
# fresh External-template axioms by Lean name
ext = {}
for d in dirs:
    for f in ('FunsExternal_Template.lean', 'TypesExternal_Template.lean'):
        p = os.path.join(d, f)
        if os.path.exists(p):
            for m in re.finditer(r'(?m)^\s*(?:@\[[^\]]*\]\s*)*axiom\s+(\S+)', G.uncomment(open(p).read())):
                ext.setdefault(m.group(1), []).append(dict(dir=os.path.relpath(d, EV), file=f))
gtext = {m: Path(f'inputs/gate/{m}.lean').read_text() for m in CL}
def refs(name):
    out = []
    for m in CL:
        for full in P[m]['reached_definitions']:
            n = full.split('.', 1)[1] if '.' in full else full
        body = gtext[m]
        # reached definitions of module m whose block mentions name
        for b in G.parse_blocks(body):
            if b['kind'] == 'decl' and b['name'] != name and re.search(r'(?<![\w.])' + re.escape(name) + r'(?![\w])', b['body']):
                ns = 'FIq_Native' if m.startswith('RPu') else ('AspisR1PoseidonPreparedSum3Source' if 'PreparedSum3' in m else 'AspisR1SelectedMaskProbe')
                full = ns + '.' + b['name']
                if full in P[m]['reached_definitions']: out.append(dict(module=m, definition=full))
    return out
entries = []
for m in CL:
    t = gtext[m]
    blocks = G.parse_blocks(t)
    for b in blocks:
        txt = b['text']
        if b['kind'] == 'decl':
            if 'Source:' in txt or 'Name pattern' in txt: continue
            origin = 'hand-written declaration (no Aeneas Source: doc comment)'
            name = b['name']
        else:
            mm = re.search(r'(?m)^(abbrev|def|instance|theorem)\s+(\S+)', txt)
            if not mm or 'Source:' in txt or '/-- [' in txt or 'Name pattern' in txt: continue
            origin = 'hand-written line in the Aeneas-generated header region'
            name = mm.group(2)
        entries.append(dict(
            gate_module=m, gate_file=GS[m]['paths'][0], gate_file_sha256=GS[m]['shas'][0], external_name=name, origin=origin, gate_definition=txt.strip(),
            fresh_form=('External-template axiom in usable fresh emission(s): ' + json.dumps(ext[name])) if name in ext else 'absent from the External templates of the usable fresh emissions (not an Aeneas external there)',
            pinned_crate=(TOOLCHAIN if re.match(r'(core|Array|MutAArray|revFold|rangeFold|range_clone)', name) else 'in-tree helper of the probe crate / statement crate; frozen Cargo.lock path-crates (aspis-statement, aspis-core), no registry crate'),
            resolved_as_hand_written_model=True, dependent_reached_definitions=refs(name)[:40]))
# gate Aeneas-translated definitions whose fresh form is an External-template axiom
for m in CL:
    for full, e in ST['modules'].get(m, {}).get('reached', {}).items():
        if e['status'] == 'FRESH_EXTERNAL_AXIOM_ONLY':
            n = full.split('.', 1)[1]
            blk = [b for b in G.parse_blocks(gtext[m]) if b['kind'] == 'decl' and b['name'] == n]
            entries.append(dict(gate_module=m, gate_file=GS[m]['paths'][0], gate_file_sha256=GS[m]['shas'][0], external_name=full, origin='Aeneas-translated definition of the probe crate (has a Source: doc comment), not hand-written',
                                gate_definition=blk[0]['text'].strip() if blk else None, fresh_form='External-template axiom (opaque) in the usable fresh emission: ' + json.dumps(e['fresh']),
                                pinned_crate='aspis-core (frozen path crate), function body present in the frozen source', resolved_as_hand_written_model=False,
                                dependent_reached_definitions=refs(n)[:40]))
Path('PCUB_HAND_MODELS.json').write_text(json.dumps(dict(
    note='Record only; no trust row is added or proposed. An entry is a name that the fresh-versus-gate comparison (or a gate definition in this cluster) resolves to a gate-side definition that is hand-written (resolved_as_hand_written_model true) or an Aeneas-translated gate definition whose fresh counterpart is an opaque External axiom (false). Fresh-side External templates were read from the usable overflow-checks-on emissions only. No compared theorem of this job (Native01 x5, Native11 x1, NativeTypes x8) depends on any entry except as listed in dependent_reached_definitions of the entry: the compared bodies (field.P, M31.add/sub/double, mul_by_r, POOL_V1_TREE_DEPTH) call only each other, and the compared types are structures over Std.U8/U64/U32/Array.',
    entries=entries), indent=1))
# ---- provenance record
prov = {}
G_PAR = {b['name']: G.norm_decl(b) for b in G.parse_blocks(Path('inputs/parent/RPz4_SelectedMaskFuns.lean').read_text()) if b['kind'] == 'decl'}
for m in CL:
    bl = [b for b in G.parse_blocks(gtext[m]) if b['kind'] == 'decl']
    same = [b['name'] for b in bl if b['name'] in G_PAR and G_PAR[b['name']] == G.norm_decl(b)]
    hdr = gtext[m].split('\n')[0][:200]
    reached = ST['modules'].get(m, {}).get('reached', {})
    cnt = ST['modules'].get(m, {}).get('counts', {})
    proved = [k for k, e in reached.items() if e['status'].startswith('PROVED')]
    if proved: cls = 'TRANSFORMATION_OF_FRESH_EMISSION_FOR_THE_PROVED_DEFINITIONS (definition level; the module as a whole is not an emission)'
    else: cls = 'HAND_TRANSFORMED_NO_FRESH_COUNTERPART'
    prov[m] = dict(classification=cls, kind=P[m]['kind'], partition_group=P[m]['group'], gate_files=GS[m], n_declarations=len(bl),
                   declarations_byte_equal_to_retained_parent_G_RPz4_SelectedMaskFuns=sorted(same), first_line=hdr,
                   header_claims_slice=('byte-for-byte' in gtext[m][:600] or 'byte-identical' in gtext[m][:600] or 'Exact' in gtext[m][:300]),
                   reached_status_counts=cnt, proved_definitions=proved,
                   nearest_fresh_emission_differences=('none of the definitions that have a fresh counterpart differ: the compared bodies are text-identical after the header/namespace wrapper (generator normalized text) and Lean-equal (see theorems)' if proved else
                                                       'no usable fresh frozen emission contains any reached definition of this module, so there is no nearest emission to diff against; routed to P4 spec C001 (module list) / C005 (RPu_FIq_NativeTypes) in PCO_extract_specs.json'))
Path('PCUB_PROVENANCE.json').write_text(json.dumps(dict(target_established=False, parent_G_used='research:evidence/replay-dry5-20261026/RPz4_SelectedMaskFuns.lean (module AspisR1SelectedMaskProbe.Funs, partition group R): only a name-and-normalized-text containment test, not a claim about its provenance',
                                                          modules=prov), indent=1))
print(len(entries), 'hand-model entries'); print({m: v['classification'][:30] for m, v in prov.items()})
