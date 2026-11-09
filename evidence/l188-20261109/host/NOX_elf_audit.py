#!/usr/bin/env python3
"""NOX_ ELF audit (T1 diff + T3). Read-only over own build outputs and the pinned
reference copies; writes JSON to own workspace. Association by symbol name and
build provenance only; NOT a semantic proof."""
import hashlib, json, re, subprocess, sys, collections
from pathlib import Path
W = Path('/home/dombarker/project-offloads/codex-cx-l188-20261109')
L = Path('/home/dombarker/.cache/solana/v1.52/platform-tools/llvm/bin')
OUT = W / 'analysis'; OUT.mkdir(exist_ok=True)
sha = lambda p: hashlib.sha256(Path(p).read_bytes()).hexdigest()
def run(*a):
    return subprocess.run([str(x) for x in a], capture_output=True, text=True, check=True).stdout
NAME = 'aspis_r1_cost_probe_program.so'
builds = {
 'B001_default_fjd': W/'out/NOX_B001/artifacts'/NAME,
 'B002_default_plain': W/'out/NOX_B002/artifacts'/NAME,
 'B003_devnet_plain': W/'out/NOX_B003/artifacts'/NAME,
}
linked = {
 'B001_default_fjd': W/'target/NOX_B001/sbpf-solana-solana/release'/NAME,
 'B002_default_plain': W/'target/NOX_B002/sbpf-solana-solana/release'/NAME,
 'B003_devnet_plain': W/'target/NOX_B003/sbpf-solana-solana/release'/NAME,
}
refs = {
 'NCR_B003_default_pin': Path('/home/dombarker/project-offloads/codex-cx-native-elfscope-20261028/NCR_B003/artifacts')/NAME,
 'NCY_B001_devnet_pin': Path('/home/dombarker/project-offloads/codex-cx-native-elfpins-20261028/NCY_B001/artifacts')/NAME,
 'NDZ_devnet_deployed_copy': Path('/home/dombarker/project-offloads/codex-cx-devnet-rehearse-20261029/evidence/devnet-rehearse-20261029')/NAME,
}
PINS = {'default': 'f8c0ec72621fd5029a97d796c4a3623d0dc44a8e7074122372f9872915d143d4',
        'devnet': '63ad3e9cc096dcbb55b3ca7ac7c8e89e6a845796ab5e4f5b7d15db96f3784299'}
res = {'schema': 'NOX_ELF_AUDIT/1', 'note': 'association by symbol name and build provenance; not a semantic proof', 'hashes': {}}
allp = dict(builds); allp.update({'linked_'+a: b for a, b in linked.items()}); allp.update(refs)
for k, p in allp.items():
    res['hashes'][k] = {'path': str(p), 'exists': p.exists(), 'sha256': sha(p) if p.exists() else None, 'bytes': p.stat().st_size if p.exists() else None}

def sections(p):
    txt = run(L/'llvm-readelf', '-SW', p)
    secs = []
    for line in txt.splitlines():
        m = re.match(r'\s*\[\s*(\d+)\]\s+(\S*)\s+(\S+)\s+([0-9a-f]+)\s+([0-9a-f]+)\s+([0-9a-f]+)\s+\S+\s+(\S*)', line)
        if m and m.group(1) != '0':
            secs.append(dict(idx=int(m.group(1)), name=m.group(2), type=m.group(3), addr=int(m.group(4),16), off=int(m.group(5),16), size=int(m.group(6),16), flags=m.group(7)))
    data = Path(p).read_bytes()
    for s in secs:
        if s['type'] != 'NOBITS':
            s['sha256'] = hashlib.sha256(data[s['off']:s['off']+s['size']]).hexdigest()
    return secs, txt

def diff(a, b):
    da, db = Path(a).read_bytes(), Path(b).read_bytes()
    sa, _ = sections(a); sb, _ = sections(b)
    offs = [i for i in range(min(len(da), len(db))) if da[i] != db[i]]
    def where(o, secs):
        for s in secs:
            if s['type'] != 'NOBITS' and s['off'] <= o < s['off']+s['size']:
                return s['name']
        return '<header/padding>'
    per = collections.Counter(where(o, sa) for o in offs)
    runs = []
    for o in offs:
        if runs and o <= runs[-1][1] + 8: runs[-1][1] = o
        else: runs.append([o, o])
    return {'len_a': len(da), 'len_b': len(db), 'differing_bytes': len(offs), 'by_section_of_a': dict(per),
            'runs': [{'start': r[0], 'end': r[1], 'section': where(r[0], sa), 'a_hex': da[r[0]:r[1]+1].hex()[:128], 'b_hex': db[r[0]:r[1]+1].hex()[:128]} for r in runs[:80]],
            'section_tables_equal': [(x['name'], x['size'], x['off']) for x in sa] == [(x['name'], x['size'], x['off']) for x in sb],
            'section_hash_diff': [x['name'] for x, y in zip(sa, sb) if x.get('sha256') != y.get('sha256')]}

res['diff_B001_vs_B002'] = diff(builds['B001_default_fjd'], builds['B002_default_plain'])
res['diff_B002_default_vs_B003_devnet'] = diff(builds['B002_default_plain'], builds['B003_devnet_plain'])
res['diff_linked_B001_vs_B002'] = diff(linked['B001_default_fjd'], linked['B002_default_plain'])

per_elf = {}
for k in ['B002_default_plain', 'B003_devnet_plain']:
    p, lp = builds[k], linked[k]
    e = {}
    e['header'] = run(L/'llvm-readelf', '-hW', p)
    e['program_headers'] = run(L/'llvm-readelf', '-lW', p)
    secs, stxt = sections(p); e['sections'] = secs; e['sections_text'] = stxt
    e['dynsyms_text'] = run(L/'llvm-readelf', '--dyn-syms', '-W', '--demangle', p)
    e['relocs_text'] = run(L/'llvm-readelf', '-rW', p)
    e['dynamic_text'] = run(L/'llvm-readelf', '-dW', p)
    und = set(); defined_dyn = []
    for line in e['dynsyms_text'].splitlines():
        parts = line.split()
        if len(parts) >= 8 and parts[0].rstrip(':').isdigit():
            nm = ' '.join(parts[7:])
            if parts[6] == 'UND' and nm: und.add(nm)
            elif parts[6] != 'UND': defined_dyn.append({'name': nm, 'type': parts[3], 'value': parts[1], 'size': parts[2]})
    reloc_targets = collections.Counter()
    for line in e['relocs_text'].splitlines():
        parts = line.split()
        if len(parts) >= 5 and re.match(r'^[0-9a-f]+$', parts[0]): reloc_targets[parts[-1]] += 1
    e['undefined_dynamic_imports'] = sorted(und)
    e['syscall_imports'] = {n: reloc_targets.get(n, 0) for n in sorted(und) if n.startswith(('sol_', 'abort', 'custom_panic'))}
    e['defined_dynamic_symbols'] = defined_dyn
    e['rodata'] = [s for s in secs if s['name'].startswith('.rodata') or s['name'].startswith('.data')]
    # linked (unstripped) symbol table: function definitions
    st = run(L/'llvm-readelf', '-sW', lp)
    stdm = run(L/'llvm-readelf', '-sW', '--demangle', lp)
    funcs = []
    for raw, dm in zip(st.splitlines(), stdm.splitlines()):
        a, b = raw.split(), dm.split()
        if len(a) >= 8 and a[0].rstrip(':').isdigit() and a[3] == 'FUNC' and a[6] != 'UND':
            funcs.append({'mangled': a[7], 'demangled': ' '.join(b[7:]), 'value': a[1], 'size': int(a[2]) if a[2].isdigit() else int(a[2], 16), 'bind': a[4]})
    e['linked_function_symbols'] = funcs
    e['linked_function_count'] = len(funcs)
    e['entrypoint_symbols'] = [f for f in funcs if f['mangled'] == 'entrypoint' or 'entrypoint' in f['demangled']]
    per_elf[k] = e
res['elf'] = {k: {kk: vv for kk, vv in v.items() if kk not in ('linked_function_symbols',)} for k, v in per_elf.items()}
(OUT/'NOX_FUNCS_default.json').write_text(json.dumps(per_elf['B002_default_plain']['linked_function_symbols'], indent=0))
(OUT/'NOX_FUNCS_devnet.json').write_text(json.dumps(per_elf['B003_devnet_plain']['linked_function_symbols'], indent=0))

# Stack-offset diagnostics vs linked symbols (freeze-20261020 method)
for k, att in [('B002_default_plain', 'NOX_B002'), ('B003_devnet_plain', 'NOX_B003')]:
    err = (W/'receipts'/att/'stderr.log').read_text(errors='replace') + (W/'receipts'/att/'stdout.log').read_text(errors='replace')
    names = {f['mangled'] for f in per_elf[k]['linked_function_symbols']}
    relt = per_elf[k]['relocs_text']
    diags = []
    for line in err.splitlines():
        m = re.search(r'Function (\S+) Stack offset of (\d+) exceeded max offset of (\d+) by (\d+) bytes.*?frame size: (\d+)', line)
        if m:
            s = m.group(1)
            diags.append({'symbol': s, 'offset': int(m.group(2)), 'limit': int(m.group(3)), 'excess': int(m.group(4)), 'frame': int(m.group(5)),
                          'in_linked_symtab': s in names, 'in_stripped_relocs': s in relt,
                          'classification': 'PRESENT_IN_LINKED_ELF_REVIEW_REQUIRED' if (s in names or s in relt) else 'ABSENT_FROM_LINKED_ELF'})
    uniq = {d['symbol']: d for d in diags}
    res.setdefault('stack', {})[k] = {'diagnostics': len(diags), 'unique_symbols': len(uniq),
        'present_in_linked': sorted(s for s, d in uniq.items() if d['classification'].startswith('PRESENT')),
        'records': list(uniq.values())}

# Name association of gate selections to linked function symbols
sel = json.loads((W/'NOX_selections.json').read_text())
extra = ['compact::expand_values', 'candidate::query_values', 'multiproof::verify_in_place', 'owned::stage1_owned', 'owned::stage2_owned',
         'owned::stage1', 'owned::stage2', 'process_r1_cost_probe_instruction', 'verifier::update_residue_row', 'sampler::add_small_base_p',
         'sampler::low_base_p_digits', 'BatchedWeights::finish', 'candidate_claims::claims', 'authenticate_asq8_accounts', 'validate_asq8',
         'fast_pairing::canonical::reduce', 'EbyKDot::push', 'EbyKDot::finish', 'Dot::finish', 'Variant::row', 'heap::filled', 'transport::order']
def keys_from_def(d):
    parts = d.split('.')
    if parts and parts[0][:1].isupper() and len(parts) > 2: parts = parts[1:]
    parts = [x for x in parts if x not in ('body', 'impl') and not x.startswith(('closure', 'Insts', 'Core'))]
    parts = [re.sub(r'_loop\d*$', '', x) for x in parts]
    parts = [x for x in parts if x not in ('aspis_core',)]
    if len(parts) < 2: return None
    return '::'.join(parts[-2:])
targets = collections.OrderedDict()
for s in sel:
    for r in s['roots']:
        k = '::'.join([x for x in r.split('::') if x not in ('crate', '_')][-2:]); targets.setdefault(k, set()).add(s['spec'])
    for d in s['defs']:
        k = keys_from_def(d)
        if k: targets.setdefault(k, set()).add(s['spec'])
for x in extra: targets.setdefault(x, set()).add('lead-brief')
funcs = per_elf['B002_default_plain']['linked_function_symbols']
assoc = []
for k, specs in targets.items():
    if not k: continue
    pat = re.compile(r'(^|::|<)' + re.escape(k) + r'(::h[0-9a-f]{16}|$|::\{\{closure\}\})')
    hits = [f for f in funcs if pat.search(f['demangled'])]
    # generic-impl spelling: <aspis_core::field::M31 as core::ops::Add>::add etc.
    if not hits and '::' in k:
        ty, meth = k.split('::')[-2:]
        hits = [f for f in funcs if re.search(r'\b' + re.escape(ty) + r'\b', f['demangled']) and re.search(r'>::' + re.escape(meth) + r'(::h|$)', f['demangled'])]
    assoc.append({'key': k, 'specs': sorted(specs), 'linked_symbols': [{'demangled': h['demangled'], 'size': h['size']} for h in hits][:12],
                  'status': 'NAMED_SYMBOL_PRESENT' if hits else 'NOT_INDIVIDUALLY_IDENTIFIABLE (inlined, merged, or dead-stripped; no DWARF inline map)'})
res['association'] = {'method': 'demangled linked .symtab name match on the last two Rust path components; impl-trait spelling fallback; no DWARF (strip=debuginfo); not a semantic proof',
    'targets': len(assoc), 'present': sum(a['status'].startswith('NAMED') for a in assoc), 'records': assoc}
(OUT/'NOX_ELF_AUDIT.json').write_text(json.dumps(res, indent=1, default=list))
print(json.dumps({'hashes': res['hashes'], 'diff_B001_B002': {k: res['diff_B001_vs_B002'][k] for k in ('differing_bytes', 'by_section_of_a', 'section_tables_equal', 'section_hash_diff')},
  'diff_default_devnet': {k: res['diff_B002_default_vs_B003_devnet'][k] for k in ('differing_bytes', 'by_section_of_a', 'section_tables_equal', 'section_hash_diff')},
  'syscalls': {k: v['syscall_imports'] for k, v in res['elf'].items()}, 'linked_funcs': {k: v['linked_function_count'] for k, v in res['elf'].items()},
  'stack': {k: {'diags': v['diagnostics'], 'unique': v['unique_symbols'], 'present': v['present_in_linked']} for k, v in res['stack'].items()},
  'assoc': {'targets': res['association']['targets'], 'present': res['association']['present']}}, indent=1))
