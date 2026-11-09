#!/usr/bin/env python3
"""PCO_make_specs.py: derive PCO_extract_specs.json from PCO_PARTITION.json.

One spec = one Charon+Aeneas run: {crate, manifest at the frozen revision, start_from roots, include/opaque lists, features,
namespace, covers}. Specs are grouped by (frozen crate, features, top-level Rust source module). Roots are the function
items among the reached definitions (type and constant items are pulled in by reachability); impl items use the
`crate::<module>::_::<fn>` wildcard selector style of NMH_E013/E024. Closures and loop expansions map to their parent.
Kinds
  frozen     runnable by PCO_render_spec.py / PCO_run.py (P1a: aspis-core, aspis-statement; P1b: probe, program, mapped cut items)
  cut        definitions whose Rust item has no counterpart in the frozen tree (probe/cut crates): routed to P4
  reference  group (b) reference-crate configurations: routed to P4 (b2 has a committed source, b1/b3 are listed for completeness)
Modules of group c0 (hand-transformed copies, no annotated definition) get kind `manual` entries in `unmapped`.
Usage: PCO_make_specs.py PCO_PARTITION.json PCO_PILOT_SPECS.json OUT.json"""
import json, re, sys, collections
from pathlib import Path
part = json.loads(Path(sys.argv[1]).read_text()); pilots = json.loads(Path(sys.argv[2]).read_text())['specs']
FROZEN_MAN = {  # source-path prefix -> (crate label, manifest, features, start_from path prefix, half)
 'crates/aspis-core/': ('aspis-core', 'crates/aspis-core/Cargo.toml', 'r0', 'crate', 'P1a'),
 'crates/aspis-statement/': ('aspis-statement', 'crates/aspis-r1-cost-probe/Cargo.toml', 'private-leaf-salts,optimized-terminal,program-build', 'aspis_statement', 'P1a'),
 'crates/aspis-r1-cost-probe/': ('aspis-r1-cost-probe', 'crates/aspis-r1-cost-probe/Cargo.toml', 'private-leaf-salts,optimized-terminal,program-build', 'crate', 'P1b'),
 'programs/r1-cost-probe/': ('aspis-r1-cost-probe-program', 'programs/r1-cost-probe/Cargo.toml', 'pool-adapter,private-leaf-salts', 'crate', 'P1b'),
 'programs/aspis-pool/': ('aspis-pool-program', 'programs/aspis-pool/Cargo.toml', 'r1-split-checkpoint,pair-forest-source-invariant-audit,pair-forest-source-result-invariant-audit', 'crate', 'P1b'),
}
def is_fn_symbol(rust):
    r = re.sub(r'\{[^{}]*\}', '{}', rust)
    last = r.split('::')[-1]
    if last.startswith('closure') or '#' in last: return False
    return bool(re.match(r'^[a-z_][a-z0-9_]*$', last))
def to_root(rust, prefix):
    """CRATE::field::{CRATE::field::M31}::neg -> crate::field::_::neg"""
    r = re.sub(r'\{[^{}]*\}', '_', re.sub(r'\{[^{}]*\}', '_', rust))
    parts = [p for p in r.split('::') if p]
    assert parts[0] == 'CRATE'
    return '::'.join([prefix] + parts[1:])
def src_prefix(src):
    if not src: return None
    for p in FROZEN_MAN:
        if src.startswith(p): return p
    return None
mods = part['modules']
groups = collections.defaultdict(lambda: dict(roots=set(), modules=set(), defs=[]))
cut = collections.defaultdict(lambda: dict(modules=set(), defs=[]))
unmapped = []
for m, rec in sorted(mods.items()):
    g = rec['group']; sg = rec['subgroup']
    if g != 'c' or sg.startswith('c1'): continue
    if sg.startswith('c0'): unmapped.append(dict(module=m, reason='c0: no annotated definition reached; hand-transformed copy, manual mapping')); continue
    for dn, d in rec['reached_definitions'].items():
        if d['coverage'] not in ('UNCOVERED', 'COVERED_DIFFERS'): continue
        sp = src_prefix(d['source'])
        if sp is None:
            cut[(rec['crates'][0] if rec['crates'] else '?', rec['kind'])]['modules'].add(m); cut[(rec['crates'][0] if rec['crates'] else '?', rec['kind'])]['defs'].append(dict(module=m, definition=dn, rust=d['rust'], source=d['source'])); continue
        crate, man, feat, pre, half = FROZEN_MAN[sp]
        top = [re.sub(r'\.rs$', '', d['source'][len(sp):]).replace('src/', '', 1)]
        key = (crate, man, feat, pre, half, top[0] if top else '')
        gg = groups[key]; gg['modules'].add(m); gg['defs'].append(dict(module=m, definition=dn, rust=d['rust'], source=d['source']))
        if is_fn_symbol(d['rust']): gg['roots'].add(to_root(d['rust'], pre))
specs = []; n = 0
for p in pilots: specs.append(p)
for key, gg in sorted(groups.items(), key=lambda x: (x[0][4], x[0][0], x[0][5])):
    crate, man, feat, pre, half, top = key
    n += 1
    specs.append(dict(spec_id='S%03d' % n, kind='frozen' if gg['roots'] else 'frozen_types_only', label=f'{crate}:{top}', crate=crate, manifest=man, features=feat,
                      start_from=sorted(gg['roots']), include=[], opaque=[], namespace=re.sub(r'[^A-Za-z0-9_]', '_', f'PCO_{crate}_{top}'), p1_half=half,
                      roots_needed=(None if gg['roots'] else 'types only: no function item among the uncovered/differing definitions of this source file. Take the roots from the callers of these types (the sibling Funs modules of the covered Type modules), as done for pilot S903.'),
                      covers=dict(modules=sorted(gg['modules']), definitions=[d['definition'] for d in gg['defs']], rust_symbols=sorted({d['rust'] for d in gg['defs']})),
                      basis='Derived from PCO_PARTITION.json reached definitions that are UNCOVERED or COVERED_DIFFERS; roots are the function items; include/opaque lists are empty and must be reviewed per spec (the NMH specs for the same functions are the starting point).'))
cn = 0
for (crate, kind), cc in sorted(cut.items()):
    cn += 1
    specs.append(dict(spec_id='C%03d' % cn, kind='cut', label=f'cut crate {crate} ({kind})', crate=crate, p1_half='P4', route='P4',
                      covers=dict(modules=sorted(cc['modules']), definitions=[d['definition'] for d in cc['defs']], rust_symbols=sorted({d['rust'] for d in cc['defs']})),
                      basis='Source path of the reached definitions is not under a frozen crate: no frozen counterpart. The cut crate source (or a re-route of the parent bridge to the frozen function) is a P4 decision.'))
# reference configurations (group b)
refs = collections.defaultdict(lambda: dict(modules=[], subgroups=set(), crates=set()))
for m, rec in mods.items():
    if rec['group'] != 'b': continue
    ns = m.split('.')[0]
    refs[ns]['modules'].append(m); refs[ns]['subgroups'].add(rec['subgroup']); refs[ns]['crates'].update(rec['crates'])
rn = 0
for ns, rr in sorted(refs.items()):
    rn += 1
    specs.append(dict(spec_id='R%03d' % rn, kind='reference', label=f'reference namespace {ns}', crate=sorted(rr['crates']) , p1_half='P4', route='P4',
                      source_status=sorted(rr['subgroups']), covers=dict(modules=sorted(rr['modules'])),
                      basis='Group (b) reference crate emission; b2 has a committed source not linked to the emission, b1 is hash-linked, b3 source not located by the bounded search. Reconstruct or re-route (P4).'))
out = dict(schema=1, target_established=False, partition_revision=part['basis'].get('research_revision'), specs=specs, unmapped=unmapped,
           counts=dict(frozen=sum(1 for s in specs if s['kind'] == 'frozen'), frozen_types_only=sum(1 for s in specs if s['kind'] == 'frozen_types_only'), cut=sum(1 for s in specs if s['kind'] == 'cut'),
                       reference=sum(1 for s in specs if s['kind'] == 'reference'), pilots=len(pilots), unmapped_modules=len(unmapped)))
Path(sys.argv[3]).write_text(json.dumps(out, indent=1) + '\n'); print(json.dumps(out['counts']))
