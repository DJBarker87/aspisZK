"""PIN2 W4 fixture regeneration driver (proof-byte layer).

Re-runs the ORIGINAL joint-fixture generators (taken verbatim from research,
blob-pinned below) with exactly two kinds of textual substitution: the input
path (transfer-13 fixture -> this directory's inputs/) and the input sha256
pins (old -> PIN2).  Everything else in each generator, including its region
geometry, row table and proof text, is unchanged.  Outputs are renamed to the
release module names by replacing only the import header with the release
source's import header (the NDO_/RPz8_ port changed imports only).

  python3 -I PIN2W4_regen.py check   # old inputs: must reproduce the release sources byte for byte
  python3 -I PIN2W4_regen.py pin2    # PIN2 inputs: writes sources/ and REGEN.json
"""
import hashlib, json, shutil, subprocess, sys, tempfile
from pathlib import Path
HERE = Path(__file__).resolve().parent
ZK = '/Users/dominic/ZK'
REL = 'docs/research/100bit-spend-path-20261013/evidence/pin2-w4-20261111'
OLDFX = 'docs/research/100bit-spend-path-20261013/evidence/format-adopt-20261019/fixtures/transfer-13'
GENS = ['evidence/joint-fixture-20261026/JFx_generate_data.py',
        'evidence/joint-fixture3-20261026/JFz_generate_scan.py',
        'evidence/joint-fixture3-20261026/JFz_generate_rows.py',
        'evidence/joint-fixture4-20261026/JFw_generate_records.py']
AUX = ['evidence/joint-fixture-20261026/JFx_DATA.json',
       'evidence/joint-fixture3-20261026/JFz_SCAN_MANIFEST.json',
       'evidence/joint-fixture3-20261026/JFz_ROWS_MANIFEST.json',
       'evidence/joint-fixture4-20261026/JFw_RECORDS_MANIFEST.json']
OLD = {'proof': '55386c507d3feeebfc45272a1cf15c33ccb9ccf0a8a8f41180fc654d806fff6f',
       'public': 'f6bcd49446f1077d2c5ed4be940e91f0be444efc5ae83024ec0700b8c205c331',
       'checkpoint': '6c9f774dd0032d3df18c9724c38d02c5225f31808a4cfe8560c210dc4d3dc625'}
sha = lambda b: hashlib.sha256(b).hexdigest()
git = lambda *a: subprocess.run(['git', '-C', ZK, *a], capture_output=True, check=True).stdout

def release_path(mod):
    for p in (f'lean/{mod}.lean', f'evidence/replay-dry9-20261027/{mod}.lean'):
        try:
            git('cat-file', '-e', f'research:{p}'); return p
        except subprocess.CalledProcessError:
            pass
    raise KeyError(mod)

def release_name(jf, closure):
    for c in (f'NDO_{jf}', f'RPz8_{jf}', jf):
        if c in closure: return c
    raise KeyError(jf)

def split_header(text):
    lines = text.split('\n'); i = 0
    while i < len(lines) and lines[i].startswith('import '): i += 1
    return lines[:i], '\n'.join(lines[i:])

STMT_GENS = ['evidence/joint-fixture6-20261026/JFu_generate_public.py',
             'evidence/joint-fixture6-20261026/JFu_generate_metadata.py',
             'evidence/joint-fixture7-20261026/JFt_generate_digests.py',
             'evidence/joint-fixture8-20261026/JFs_generate_cells.py',
             'evidence/joint-fixture8-20261026/JFs_generate_serialized_digests.py']
STMT_OUT = ('lean/JFu_PublicDigest', 'lean/JFu_PublicMeta', 'lean/JFt_Digest', 'lean/JFs_Cell', 'lean/JFs_SerializedDigests')

def stmt(mode):
    """Statement layer: windows of the 1,880-byte statement read from the data
    module JFx_DataPublic00 (generators unchanged; they take no other input)."""
    closure = {l.split('\t')[0][:-6] for l in open(HERE.parent / 'pin2-public-binding-20261110/impact-scan/imports.tsv')}
    root = Path(tempfile.mkdtemp(prefix='pin2w4-stmt-')); (root / 'lean').mkdir()
    for g in STMT_GENS:
        (root / g).parent.mkdir(parents=True, exist_ok=True); (root / g).write_bytes(git('show', f'research:{g}'))
    names = [l.split('/')[-1][:-5] for l in git('ls-tree', '--name-only', 'research', 'lean/').decode().split('\n')
             if l.startswith(STMT_OUT) and l.endswith('.lean')]
    for n in names + ['JFx_DataPublic00']:
        (root / 'lean' / f'{n}.lean').write_bytes(git('show', f'research:lean/{n}.lean'))
    if mode == 'pin2':
        src = (HERE / 'sources' / 'RPz8_JFx_DataPublic00.lean').read_text()
        _, body = split_header(src); (root / 'lean' / 'JFx_DataPublic00.lean').write_text('import Aeneas\n' + body)
    for g in STMT_GENS:
        subprocess.run([sys.executable, '-I', str(root / g)] + (['--check'] if mode == 'check' else []), check=True, capture_output=True)
    if mode == 'check':
        print('stmt check: 5 statement generators reproduce', len(names), 'release JF sources'); return
    out = HERE / 'sources'; rep = json.loads((HERE / 'REGEN.json').read_text())
    rep['statement_generators'] = {g: git('rev-parse', f'research:{g}').decode().strip() for g in STMT_GENS}
    for n in sorted(names):
        try: release_name(n, closure)
        except KeyError:
            rep.setdefault('not_in_release_closure', []).append(n); continue
        rel = release_name(n, closure); relp = release_path(rel); want = git('show', f'research:{relp}').decode()
        hdr, _ = split_header(want); jhdr, body = split_header((root / 'lean' / f'{n}.lean').read_text())
        assert len(hdr) == len(jhdr); text = '\n'.join(hdr) + '\n' + body; changed = text != want
        if changed: (out / f'{rel}.lean').write_text(text)
        rep['modules'].append({'generated': n, 'release': rel, 'release_source': relp, 'release_sha256': sha(want.encode()),
            'pin2_sha256': sha(text.encode()), 'text_changed': changed, 'release_bytes': len(want), 'pin2_bytes': len(text), 'layer': 'statement'})
    (HERE / 'REGEN.json').write_text(json.dumps(rep, indent=2) + '\n')
    print('stmt:', len(names), 'generated;', sum(1 for m in rep['modules'] if m.get('layer') == 'statement' and m['text_changed']), 'text changed')
    shutil.rmtree(root)

def main(mode):
    if mode.startswith('stmt-'): return stmt(mode[5:])
    closure = {l.split('\t')[0][:-6] for l in open(HERE.parent / 'pin2-public-binding-20261110/impact-scan/imports.tsv')}
    root = Path(tempfile.mkdtemp(prefix='pin2w4-gen-'))
    (root / 'lean').mkdir()
    for g in GENS + AUX:
        (root / g).parent.mkdir(parents=True, exist_ok=True)
        (root / g).write_bytes(git('show', f'research:{g}'))
    blobs = {g: git('rev-parse', f'research:{g}').decode().strip() for g in GENS}
    if mode == 'check':
        (root / OLDFX).mkdir(parents=True)
        for n in ('r1-s2-proof.bin', 'r1-s2-public-asf8.bin'):
            shutil.copy(Path(ZK, OLDFX, n), root / OLDFX / n)
        # the generators' --check mode compares against the release JF sources
        for g in GENS:
            pass
        names = [l.split('/')[-1][:-5] for l in git('ls-tree', '--name-only', 'research', 'lean/').decode().split('\n')
                 if l.startswith('lean/JFx_Data') or l.startswith('lean/JFz_Scan') or l.startswith('lean/JFz_Row') or l.startswith('lean/JFw_NativeRow')]
        for n in names:
            (root / 'lean' / f'{n}.lean').write_bytes(git('show', f'research:lean/{n}.lean'))
        for g in GENS:
            subprocess.run([sys.executable, '-I', str(root / g), '--check'], check=True)
        # renaming must reproduce the release sources exactly
        bad = []
        for n in names:
            rel = release_name(n, closure)
            want = git('show', f'research:{release_path(rel)}').decode()
            hdr, _ = split_header(want); _, body = split_header((root / 'lean' / f'{n}.lean').read_text())
            if '\n'.join(hdr) + '\n' + body != want: bad.append(n)
        print('check: generators reproduce release JF sources; renamed outputs equal release sources except', bad)
        return
    pin2 = json.loads((HERE / 'INPUTS.json').read_text())['spends']['transfer']
    new = {'proof': pin2['proof_sha256'], 'public': pin2['statement_sha256'], 'checkpoint': pin2['checkpoint_post_stage1_sha256']}
    (root / REL / 'inputs').mkdir(parents=True)
    for n in ('transfer-proof.bin', 'transfer-statement.bin', 'transfer-checkpoint.bin'):
        shutil.copy(HERE / 'inputs' / n, root / REL / 'inputs' / n)
    subs = [(f'{OLDFX}/r1-s2-proof.bin', f'{REL}/inputs/transfer-proof.bin'),
            ("P/'r1-s2-proof.bin'", "P/'transfer-proof.bin'"), ("P/'r1-s2-public-asf8.bin'", "P/'transfer-statement.bin'"),
            (f"P=ROOT/'{OLDFX}'", f"P=ROOT/'{REL}/inputs'")] + [(OLD[k], new[k]) for k in OLD]
    applied = {}
    gdir = HERE / 'generators'; gdir.mkdir(exist_ok=True)
    for g in GENS:
        t = (root / g).read_text(); used = []
        for a, b in subs:
            if a in t: t = t.replace(a, b); used.append([a, b])
        (root / g).write_text(t); (gdir / Path(g).name).write_text(t)
        applied[g] = {'research_blob': blobs[g], 'substitutions': used, 'patched_sha256': sha(t.encode())}
    args = {GENS[0]: ['--checkpoint', str(root / REL / 'inputs' / 'transfer-checkpoint.bin')]}
    for g in GENS:
        subprocess.run([sys.executable, '-I', str(root / g), *args.get(g, [])], check=True)
    out = HERE / 'sources'; out.mkdir(exist_ok=True)
    report = {'generators': applied, 'inputs': new, 'modules': []}
    for f in sorted((root / 'lean').glob('*.lean')):
        n = f.stem; rel = release_name(n, closure); relp = release_path(rel)
        want = git('show', f'research:{relp}').decode()
        hdr, _ = split_header(want); jhdr, body = split_header(f.read_text())
        text = '\n'.join(hdr) + '\n' + body
        assert len(hdr) == len(jhdr), (n, hdr, jhdr)
        changed = text != want
        if changed: (out / f'{rel}.lean').write_text(text)
        report['modules'].append({'generated': n, 'release': rel, 'release_source': relp,
            'release_sha256': sha(want.encode()), 'pin2_sha256': sha(text.encode()), 'text_changed': changed,
            'release_bytes': len(want), 'pin2_bytes': len(text)})
    for a in AUX:
        shutil.copy(root / a, HERE / ('PIN2_' + Path(a).name))
    (HERE / 'REGEN.json').write_text(json.dumps(report, indent=2) + '\n')
    ch = [m['release'] for m in report['modules'] if m['text_changed']]
    print(len(report['modules']), 'modules generated;', len(ch), 'text changed;', len(report['modules']) - len(ch), 'identical to release text')
    shutil.rmtree(root)

if __name__ == '__main__':
    main(sys.argv[1])
