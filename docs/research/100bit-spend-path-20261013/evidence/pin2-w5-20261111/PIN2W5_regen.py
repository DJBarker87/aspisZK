"""PIN2 W5: regenerate the transcript-dependent leaf layers of the joint
accepted fixture from a native verifier dump.

Re-runs the ORIGINAL generators from research (blob ids recorded) in a
scratch tree.  The only substitutions are the verifier intermediate values
the generators take as input, and every one of them is read from a native
pin2-w5-dump of the run (PIN2W5_derive.py output):
  JFp_generate_queries.py, JFm_generate.py  JFp_SHA_INPUT.json seed (and the
                                             proof data modules, W4 PIN2)
  JFr_generate_{arithmetic,bytes,decoders}   JFr_coefficients.json: running/
                                             boundary/value = tag 1, alpha =
                                             tag 0 index 15+r, coefficients =
                                             proof[offset:offset+448]
  JFw_generate.py                            G = tag 4 index 27 (gamma)
  JFs_TX2_generate_points.py                 queries = tag 5 indices 10..21
  NDO_JFm_Coordinates (handwritten)          value00..24 = tag 0 indices 0..24
Outputs are renamed to release module names by replacing only the import
header with the release source's header (the NDO_ port changed imports only).

  python3 -I PIN2W5_regen.py check <DERIVED-26OCT.json>   # 26 Oct dump (4bb3b3f): must reproduce release
  python3 -I PIN2W5_regen.py pin2                          # PIN2 dump: writes sources/ and REGEN.json
"""
import hashlib, json, re, shutil, subprocess, sys, tempfile
from pathlib import Path
HERE = Path(__file__).resolve().parent
W4 = HERE.parent / 'pin2-w4-20261111'
ZK = '/Users/dominic/ZK'
sha = lambda b: hashlib.sha256(b).hexdigest()
git = lambda *a: subprocess.run(['git', '-C', ZK, *a], capture_output=True, check=True).stdout
def blob(p): return git('rev-parse', f'research:{p}').decode().strip()
def show(p): return git('show', f'research:{p}')
GENS = {
 'sha_q0': 'evidence/joint-fixture10-20261026/JFp_generate_queries.py',
 'sha_jfm': 'evidence/joint-fixture11-20261026/JFm_generate.py',
 'jfr_arith': 'evidence/joint-fixture9-20261026/JFr_generate_arithmetic.py',
 'jfr_bytes': 'evidence/joint-fixture9-20261026/JFr_generate_bytes.py',
 'jfr_dec': 'evidence/joint-fixture9-20261026/JFr_generate_decoders.py',
 'jfw_pow': 'evidence/fixture-tx2g-20261026/JFw_generate.py',
 'jfs_geo': 'evidence/fixture-tx2e-20261026/JFs_TX2_generate_points.py',
}
# Stage 2 reads stage-1 outputs (JFm_WINDOWS.json, the row-25/26 drafts).
GENS2 = {
 'jfm_src': 'evidence/joint-fixture11-20261026/JFm_sources.py',
 'jfu_claims': 'evidence/joint-fixture12-20261026/JFu_claims.py',
 'jfu_mask': 'evidence/joint-fixture12-20261026/JFu_mask.py',
 'jfu_sources': 'evidence/joint-fixture12-20261026/JFu_sources.py',
 'jfu_split': 'evidence/joint-fixture12-20261026/JFu_split.py',
 'jfu_split26': 'evidence/joint-fixture12-20261026/JFu_split26.py',
}
HELPERS = ['evidence/joint-fixture11-20261026/JFm_input.py']
GEO_TABLE = 'docs/research/100bit-spend-path-20261013/lean-candidates/query-geometry-source-values-20261020/sources/GeneratedFuns-v1.lean'
le = lambda b: [int.from_bytes(b[i:i+4], 'little') for i in range(0, len(b), 4)]
def release_name(jf):
    for c in (f'NDO_{jf}', f'RPz8_{jf}'):
        try: git('cat-file', '-e', f'research:lean/{c}.lean'); return c
        except subprocess.CalledProcessError: pass
    return None
def header(text):
    lines = text.split('\n'); i = 0
    while i < len(lines) and lines[i].startswith('import '): i += 1
    return lines[:i], '\n'.join(lines[i:])
def rename_new(text):
    """Header for a module with no release source: map each JF import to its release name."""
    imps, body = header(text)
    out = []
    for l in imps:
        m = l[7:]; r = release_name(m) if m.startswith('JF') else None
        out.append('import ' + (r or m))
    return '\n'.join(out + [body])

def tree(mode, D):
    T = Path(tempfile.mkdtemp(prefix='w5regen-', dir='/private/tmp/claude-501/-Users-dominic-ZK/3db59790-41f3-4c53-ae90-3fc42a8cab96/scratchpad'))
    (T / 'lean').mkdir()
    for f in git('ls-tree', '--name-only', 'research', 'lean/').decode().split():
        n = f[5:]
        if re.fullmatch(r'JF(p_SHA256|x_DataProof\d\d|w_NativeRow\d\d|z_Scan\d\d)\.lean', n):
            (T / f).write_bytes(show(f))
    for g in [*GENS.values(), *GENS2.values(), *HELPERS]:
        (T / g).parent.mkdir(parents=True, exist_ok=True); (T / g).write_bytes(show(g))
    (T / GEO_TABLE).parent.mkdir(parents=True, exist_ok=True); (T / GEO_TABLE).write_bytes(show(GEO_TABLE))
    (T / 'evidence/joint-fixture11-20261026/JFm_UNCHECKED').mkdir(exist_ok=True)
    if mode == 'pin2':
        # W4's PIN2 proof data and scans (only literals changed); DataProof14 text-identical.
        for f in (W4 / 'sources').glob('*.lean'):
            m = re.fullmatch(r'(?:NDO_|RPz8_)(JF(?:x_DataProof\d\d|z_Scan\d\d))\.lean', f.name)
            if m: (T / 'lean' / (m[1] + '.lean')).write_bytes(f.read_bytes())
        seedjson = (W4 / 'PIN2_JFp_SHA_INPUT.json').read_bytes()
        proof = (HERE / 'inputs/transfer-proof.bin').read_bytes()
    else:
        seedjson = show('evidence/joint-fixture10-20261026/JFp_SHA_INPUT.json')
        proof = show('docs/research/100bit-spend-path-20261013/evidence/format-adopt-20261019/fixtures/transfer-13/r1-s2-proof.bin')
        assert sha(proof) == '55386c507d3feeebfc45272a1cf15c33ccb9ccf0a8a8f41180fc654d806fff6f'
    (T / 'evidence/joint-fixture10-20261026/JFp_SHA_INPUT.json').write_bytes(seedjson)
    assert json.loads(seedjson)['seed'] == D['seed_hex'], 'seed input differs from the native seed'
    # proof bytes parsed from the data modules must equal the run's proof
    raw = []
    for f in sorted((T / 'lean').glob('JFx_DataProof*.lean')):
        for line in f.read_text().splitlines():
            if line.startswith('def c'):
                if 'replicate' in line:
                    n, v = map(int, re.search(r'replicate (\d+) (\d+)#u8', line).groups()); raw += [v] * n
                else: raw += list(map(int, re.findall(r'(\d+)#u8', line)))
    assert bytes(raw) == proof, 'data modules differ from the proof file'
    # dump-sourced substitutions
    t0, t1 = D['tx1']['0'], D['tx1']['1']
    old = json.loads(show('evidence/joint-fixture9-20261026/JFr_coefficients.json'))
    coeff = [dict(round=c['round'], offset=c['offset'],
                  coefficients=[le(proof[c['offset']+16*j:c['offset']+16*j+16]) for j in range(28)],
                  running=t1[str(3*c['round'])][:4], boundary=t1[str(3*c['round']+1)][:4], value=t1[str(3*c['round']+2)][:4],
                  alpha=t0[str(15+c['round'])][:4]) for c in old]   # round/offset geometry is unchanged (W4)
    (T / 'evidence/joint-fixture9-20261026/JFr_coefficients.json').write_text(json.dumps(coeff, indent=2) + '\n')
    if mode == 'check':
        assert (T / 'evidence/joint-fixture9-20261026/JFr_coefficients.json').read_bytes() == show('evidence/joint-fixture9-20261026/JFr_coefficients.json'), 'JFr_coefficients from the dump differ from release'
    else:
        dst = HERE / 'generated/evidence/joint-fixture9-20261026/JFr_coefficients.json'; dst.parent.mkdir(parents=True, exist_ok=True)
        dst.write_bytes((T / 'evidence/joint-fixture9-20261026/JFr_coefficients.json').read_bytes())
    g = T / GENS['jfw_pow']; s = g.read_text()
    s2 = re.sub(r'^G=\[.*?\]$', 'G=[' + ','.join(map(str, D['tx1']['4']['27'])) + ']', s, count=1, flags=re.M); assert s2 != s or mode == 'check'; g.write_text(s2)
    g = T / GENS['jfs_geo']; s = g.read_text()
    q = [D['tx1']['5'][str(i)][0] for i in range(10, 22)]
    s2 = re.sub(r'^queries=\[.*?\]$', 'queries=[' + ','.join(map(str, q)) + ']', s, count=1, flags=re.M); g.write_text(s2)
    return T, coeff

def run(T):
    before = {p: p.read_bytes() for p in T.rglob('*') if p.is_file()}
    for k, g in GENS.items():
        r = subprocess.run([sys.executable, '-I', str(T / g)], cwd=T, capture_output=True, text=True)
        assert r.returncode == 0, (g, r.stderr[-2000:])
    # The archived drafts that the JFu generators read: rows 25/26 Hashes and
    # Sources as written by the stage-1/2 JFm generators, and the row-25 block
    # split (PIN2W5_split25.py, reproduced byte for byte in check mode).
    U = T / 'evidence/joint-fixture11-20261026/JFm_UNCHECKED'
    for k in ('jfm_src',):
        r = subprocess.run([sys.executable, '-E', '-s', str(T / GENS2[k])], cwd=T, capture_output=True, text=True); assert r.returncode == 0, (k, r.stderr[-2000:])
    for n in ('JFm_Q25Hashes', 'JFm_Q26Hashes', 'JFm_Q25Source', 'JFm_Q26Source'):
        f = T / 'lean' / f'{n}.lean'; (U / f'{n}.lean.txt').write_bytes(f.read_bytes()); f.unlink()
    sys.path.insert(0, str(HERE)); from PIN2W5_split25 import split
    for f, t in split((U / 'JFm_Q25Hashes.lean.txt').read_text()).items(): (U / f).write_text(t)
    for k, g in GENS2.items():
        if k == 'jfm_src': continue
        r = subprocess.run([sys.executable, '-I', str(T / g)], cwd=T, capture_output=True, text=True)
        assert r.returncode == 0, (g, r.stderr[-2000:])
    return {p: p.read_bytes() for p in T.rglob('*') if p.is_file() and before.get(p) != p.read_bytes()}

def coordinates(D, src):
    """NDO_JFm_Coordinates: replace the 25 value literals by trace tag 0 indices 0..24."""
    def q(x): return f'⟨⟨{x[0]}#u32,{x[1]}#u32⟩,⟨{x[2]}#u32,{x[3]}#u32⟩⟩'
    out = src
    for i in range(25):
        out, n = re.subn(rf'^def value{i:02} : aspis_core\.field\.QM31 := .*$', f'def value{i:02} : aspis_core.field.QM31 := {q(D["tx1"]["0"][str(i)][:4])}', out, flags=re.M); assert n == 1
    return out

def main():
    mode = sys.argv[1]
    dpath = (Path(sys.argv[2]) if len(sys.argv) > 2 else HERE / 'provenance-26oct/DERIVED-26OCT.json') if mode == 'check' else HERE / 'PIN2W5_VALUES.json'
    D = json.loads(dpath.read_text())
    T, coeff = tree(mode, D)
    changed = run(T)
    mods = {}; other = {}
    for p, b in changed.items():
        rel = p.relative_to(T)
        if rel.parts[0] == 'lean' and rel.suffix == '.lean': mods[rel.stem] = b.decode()
        else: other[str(rel)] = b
    mods['JFm_Coordinates'] = coordinates(D, show('lean/NDO_JFm_Coordinates.lean').decode())
    report = dict(mode=mode, values=str(dpath), values_sha256=sha(dpath.read_bytes()),
                  generators={k: dict(path=g, blob=blob(g)) for k, g in [*GENS.items(), *GENS2.items(), ('helper', HELPERS[0])]},
                  geo_table=dict(path=GEO_TABLE, blob=blob(GEO_TABLE)), modules=[])
    out = HERE / 'sources'
    if mode == 'pin2': out.mkdir(exist_ok=True)
    nsame = ndiff = nnew = 0
    for jf in sorted(mods):
        text = mods[jf]
        if jf == 'JFm_Coordinates':
            rel, final = 'NDO_JFm_Coordinates', text
        else:
            rel = release_name(jf)
            if rel:
                rimps, _ = header(show(f'lean/{rel}.lean').decode()); _, body = header(text)
                final = '\n'.join(rimps + [body])
            else:
                rel, final = 'NDO_' + jf, rename_new(text)
        try: release = show(f'lean/{rel}.lean').decode()
        except subprocess.CalledProcessError: release = None
        same = release == final
        nsame += same; ndiff += (release is not None and not same); nnew += release is None
        report['modules'].append(dict(release=rel, generated_as=jf, release_exists=release is not None,
                                      text_changed=not same, sha256=sha(final.encode()),
                                      release_sha256=sha(release.encode()) if release else None))
        if mode == 'pin2' and not same: (out / f'{rel}.lean').write_text(final)
    for k, b in sorted(other.items()):
        if '__pycache__' in k: continue
        report.setdefault('other_outputs', {})[k] = sha(b)
        if mode == 'pin2':
            dst = HERE / 'generated' / k; dst.parent.mkdir(parents=True, exist_ok=True); dst.write_bytes(b)
        else:
            try: rel_ok = show(k) == b
            except subprocess.CalledProcessError: rel_ok = None
            report.setdefault('other_equal_release', {})[k] = rel_ok
    oe = report.get('other_equal_release', {})
    print(json.dumps(dict(mode=mode, modules=len(mods), identical=nsame, changed=ndiff, new=nnew,
                          other_outputs=len(report.get('other_outputs', {})), other_equal_release=sum(1 for v in oe.values() if v), other_not_equal=[k for k, v in oe.items() if not v])))
    (HERE / f'REGEN-{mode}.json').write_text(json.dumps(report, indent=1) + '\n')
    shutil.rmtree(T)
main()
