#!/usr/bin/env python3
from pathlib import Path
import hashlib, json, re
p = Path(__file__).resolve().parent
sha = lambda f: hashlib.sha256(f.read_bytes()).hexdigest()
m = json.loads((p / 'manifest.json').read_text())
assert m['schema'] == 'focused-extractor-proof-packet-v1'
assert m['compiled_objects_included'] is False
expected = {'map_theorem', 'compile_only_dependency'}
assert {e['entry_kind'] for e in m['entries']} == expected
for e in m['entries']:
    r = json.loads((p / e['receipt']).read_text())
    pre = json.loads((p / e['preflight']).read_text())
    cmd = json.loads((p / e['command']).read_text())
    log = (p / e['log']).read_text()
    s = (p / e['source']).read_text()
    assert r == e['launch_metrics'] and r['exit_status'] == 0 and r['process_swaps'] == 0
    assert r['watchdog_abort'] is None and r['foreign_lean_samples'] == []
    assert sha(p / e['source']) == e['source_sha256'] == r['source_sha256'] == pre['source_sha256']
    assert r['object_sha256'] == e['object_sha256']
    assert r['source_revision_at_launch'] == pre['source_revision']
    assert pre['controller_sha256'] == '9b827933f26ff248491bf1fd187e6d43b804686512bd49b8edacf8ea6416fab0' == sha(p / 'run_focused.py')
    assert 'LEAN_PATH=' + (p / e['profile']).read_text().strip() in cmd['argv']
    assert '-j1' in cmd['argv'] and cmd['argv'][cmd['argv'].index('-M') + 1] == '4400'
    assert pre['no_dependency_builds'] is True
    assert e['direct_imports'] == pre['direct_imports']
    for imported in e['direct_imports'].values():
        assert Path(imported['path']).is_file() and sha(Path(imported['path'])) == imported['sha256']
    if e['entry_kind'] == 'map_theorem':
        assert len(e['theorems']) == 1
        for name, ax in e['theorems'].items():
            reports = re.findall("'" + re.escape(name) + r"' depends on axioms:\s*\[(.*?)\]", log, re.S)
            assert len(reports) == 1, name
            got = set(re.findall(r'[A-Za-z][A-Za-z0-9_.]*', reports[0]))
            assert got == set(ax) and got <= {'propext', 'Classical.choice', 'Quot.sound'}
    else:
        assert e['theorems'] == {}
        assert 'depends on axioms:' not in log
    uncommented = re.sub(r'/\-.*?\-/', '', s, flags=re.S)
    uncommented = re.sub(r'--[^\n]*', '', uncommented)
    assert not re.search(r'\b(sorry|admit|axiom|native_decide)\b', uncommented)
    assert not re.search(r'set_option\s+(max|.*Heartbeats|.*RecDepth)', uncommented)
for ext in ('*.olean', '*.elf', '*.so', '*.pyc'):
    assert not list(p.rglob(ext))

# Check normalized declaration identity against the committed source-cut extraction.
ident = json.loads((p / m['source_identity']).read_text())
cut = (p / ident['reference_packet']).resolve()
assert sha(cut / 'manifest.json') == ident['sourcecut_manifest_sha256']
def norm_decl(path, start, end):
    text = path.read_text(); i = text.index(start); j = text.index(end, i)
    return re.sub(r'\s+', ' ', text[i:j]).strip()
cut_f = norm_decl(cut / 'attempt1/generated/Funs.lean', 'def field.wide_exact.WideExact.from_limbs', '/--')
owned_f = norm_decl(p / 'AspisR1S9FieldOwnedV1/Funs/sources/Funs.lean', 'def field.wide_exact.WideExact.from_limbs', '/--')
cut_t = norm_decl(cut / 'attempt1/generated/Types.lean', 'structure field.CM31 where', '\nend ')
owned_t = norm_decl(p / 'AspisR1S9FieldOwnedV1/Types/sources/Types.lean', 'structure field.CM31 where', '\nend ')
assert cut_f == owned_f and hashlib.sha256(cut_f.encode()).hexdigest() == ident['candidate_from_limbs_body_sha256'] == ident['owned_from_limbs_body_sha256']
assert cut_t == owned_t and hashlib.sha256(cut_t.encode()).hexdigest() == ident['candidate_core_field_types_sha256'] == ident['owned_core_field_types_sha256']
assert ident['from_limbs_body_equal'] is True and ident['core_field_types_equal'] is True
for line in (p / 'SHA256SUMS').read_text().splitlines():
    digest, rel = line.split('  ', 1)
    assert sha(p / rel) == digest, rel
print('PASS: source/dependency receipts and pins; transitive standard axiom audit; exact source-cut declaration identity; no compiled objects')
