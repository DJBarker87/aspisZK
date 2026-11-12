#!/usr/bin/env python3
"""X2: every bodiless declaration of one Pool emission's package (the axioms of the adapted FunsExternal and the
opaque types of TypesExternal), classed. Reads only.
Classes: std (core::, alloc::); Solana runtime (a syscall or runtime service behind the SDK call: CPI invoke and
invoke_signed, return data, sysvar get, program-address derivation, logging, memory syscalls, stack height); SDK
(any other solana_* item); derived impl (a compiler-derived impl of Aspis code); named gap (an Aspis item opaque by
name, with the exact tool message); other.
usage: fv_x2_externals.py <run dir> <gaps.json> <out.tsv>"""
import json, re, sys
from pathlib import Path
sys.path.insert(0, str(Path(__file__).resolve().parents[2] / 'aspis-freeze-20261112' / 'host'))
import fv_frz_emit_run as FRZ
RUN, GAPS, OUT = Path(sys.argv[1]), json.load(open(sys.argv[2])), sys.argv[3]
res = json.load(open(RUN / 'result.json')); pre = res['lean_prefix']
RUNTIME = re.compile(r'solana_(program|cpi)::program::(invoke|invoke_signed|invoke_unchecked|invoke_signed_unchecked|set_return_data|get_return_data)|'
                     r'solana_cpi::|::get_return_data|::set_return_data|solana_sysvar::|Sysvar|::get$|find_program_address|create_program_address|'
                     r'try_find_program_address|solana_msg::|sol_log|sol_memcmp|sol_memcpy|sol_memset|solana_program_memory::|get_stack_height|'
                     r'solana_sha256_hasher::hashv|solana_program::hash::hashv')
DERIVED = re.compile(r'\{impl core::(clone::Clone|cmp::PartialEq|cmp::Eq|marker::|fmt::Debug|default::Default|hash::Hash)')
rows = []
for mod, kinds in (('FunsExternal', ('axiom', 'opaque')), ('TypesExternal', ('axiom', 'opaque', 'structure', 'inductive', 'def'))):
    p = RUN / 'lean-src' / (pre + mod + '.lean')
    if not p.exists(): continue
    L = p.read_text().split('\n')
    for b in FRZ.blocks(p):
        body = re.sub(r'(?s)^/--.*?-/\n', '', '\n'.join(L[b['first'] - 1:b['last']])); km = FRZ.KIND.search(body)
        if not km or km.group(1) not in kinds: continue
        rust, kind, lean = b['rust'], km.group(1), km.group(2)
        top = rust.split('::')[0]
        g = GAPS.get(rust)
        if top.startswith('aspis_'):
            cls = 'named gap' if g else ('derived impl' if DERIVED.search(rust) else 'other')
        elif top in ('core', 'alloc', 'std'): cls = 'std'
        elif RUNTIME.search(rust): cls = 'Solana runtime'
        elif top.startswith('solana') or top in ('solana_program',): cls = 'SDK'
        else: cls = 'other'
        rows.append((rust, mod, lean, cls, g['message'] if g else ''))
with open(OUT, 'w') as f:
    f.write('rust_path\tlean_module\tlean_name\tclass\ttool_message\n')
    for r in rows: f.write('\t'.join(x.replace('\t', ' ') for x in r) + '\n')
import collections
print(collections.Counter(r[3] for r in rows))
for r in rows:
    if r[3] == 'other': print('other:', r[0])
