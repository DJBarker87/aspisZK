"""PIN2 W4: SHA-256 seed layer (JFp_SHABlockNN, JFp_SeedHash) for the PIN2
transfer initialisation frame (1,595 bytes = 26 SHA blocks; release: 1,530 =
25 blocks).

* JFp_generate_sha.py (research blob pinned in SHA.json) is run unchanged
  except: its two diagnostic inputs are the PIN2 frame parts (written here
  from inputs/), the literal 1530 in its length assert becomes 1595, and
  blocks=25 in its JSON output becomes 26.
* JFp_generate_seed.py hard-codes the 25-block / 58-byte-tail geometry, so it
  is re-expressed parametrically below (seed_text).  With n=1530 seed_text
  reproduces the release JFp_SeedHash text byte for byte (checked).
usage: python3 -I PIN2W4_sha.py
"""
import hashlib, json, subprocess, sys, tempfile, shutil
from pathlib import Path
HERE = Path(__file__).resolve().parent
ZK = '/Users/dominic/ZK'
git = lambda *a: subprocess.run(['git', '-C', ZK, *a], capture_output=True, check=True).stdout
ls = lambda xs: '[' + ','.join(map(str, xs)) + ']'
GEN = 'evidence/joint-fixture10-20261026/JFp_generate_sha.py'
SEEDGEN = 'evidence/joint-fixture10-20261026/JFp_generate_seed.py'

def seed_text(b):
    n = len(b); nb = (n + 9 + 63) // 64; last = nb - 1
    # head = all blocks that contain only message bytes and are followed by the
    # two blocks holding the tail and the padding (release: 23 head blocks).
    headb = nb - 2
    hl = 64 * headb; tl = n - hl; zeros = 64 * nb - n - 9
    lenbits = list((8 * n).to_bytes(8, 'big'))
    out = [*(f'import JFp_SHABlock{i:02}' for i in range(nb)), 'import JFp_SHABlocks', 'set_option autoImplicit false', 'namespace AspisR1.JFp_SeedHash', 'open JFp_SHA256']
    for i in range(nb): out += [f'theorem len{i:02} : JFp_SHABlock{i:02}.input.length=64 := by rfl', f'#print axioms len{i:02}']
    out += ['def head : List (List Nat) := [' + ','.join(f'JFp_SHABlock{i:02}.input' for i in range(headb)) + ']',
            f'def chunks : List (List Nat) := head ++ [JFp_SHABlock{headb:02}.input,JFp_SHABlock{last:02}.input]', f'def tail : List Nat := {ls(b[hl:])}',
            'def raw : List Nat := head.flatten ++ tail', f'theorem tailLength : tail.length={tl} := by rfl', '#print axioms tailLength',
            f'theorem headLength : head.flatten.length={hl} := by',
            '  simp only [head,List.length_flatten,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,' + ','.join(f'len{i:02}' for i in range(headb)) + ']',
            '  omega', '#print axioms headLength', f'theorem rawLength : raw.length={n} := by', '  simp only [raw,List.length_append,headLength,tailLength]', '#print axioms rawLength',
            f'theorem tailPad : tail ++ [128] ++ List.replicate {zeros} 0 ++ {ls(lenbits)} = JFp_SHABlock{headb:02}.input ++ JFp_SHABlock{last:02}.input := by rfl', '#print axioms tailPad',
            'theorem padded : pad raw=chunks.flatten := by', '  rw [pad,rawLength]',
            f'  change (head.flatten ++ tail) ++ [128] ++ List.replicate {zeros} 0 ++ {ls(lenbits)}=_',
            '  simp only [List.append_assoc, chunks,List.flatten_append,List.flatten_cons,List.flatten_nil,List.append_nil]',
            '  exact congrArg (fun t => head.flatten ++ t) (by simpa only [List.append_assoc] using tailPad)', '#print axioms padded',
            'theorem chunkLengths : ∀ c ∈ chunks,c.length=64 := by', '  intro c hc',
            '  simp only [chunks,head,List.mem_append,List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false,or_assoc] at hc',
            '  rcases hc with ' + '|'.join(f'h{i}' for i in range(nb))]
    for i in range(nb): out += [f'  · subst c;exact len{i:02}']
    out += ['#print axioms chunkLengths', f'theorem paddedLength : (pad raw).length={64*nb} := by', '  rw [padded]',
            f'  simp only [chunks,List.flatten_append,List.length_append,headLength,List.flatten_cons,List.flatten_nil,List.length_nil,len{headb:02},len{last:02}]',
            '#print axioms paddedLength', 'theorem blockList : blocks ((pad raw).length/64) (pad raw)=chunks := by', '  rw [paddedLength,padded]',
            '  exact blocks_chunks chunks chunkLengths', '#print axioms blockList', f'theorem checked : JFp_SHA256.hash raw=JFp_SHABlock{last:02}.result := by',
            '  unfold JFp_SHA256.hash', '  dsimp only', '  rw [blockList]', '  simp only [chunks,head,List.foldl_append,List.foldl_cons,List.foldl_nil]']
    for i in range(nb): out += ['  rw [show ' + ('initial' if i == 0 else f'JFp_SHABlock{i-1:02}.result') + f'=JFp_SHABlock{i:02}.start from rfl,JFp_SHABlock{i:02}.checked]']
    out += ['#print axioms checked', 'end AspisR1.JFp_SeedHash']
    return '\n'.join(out) + '\n'

def ndo(text):   # NDO_ port renames JF imports only
    return '\n'.join(('import NDO_' + l[7:]) if l.startswith('import JFp_') else l for l in text.split('\n'))

def main():
    rep = {'sha_generator_blob': git('rev-parse', f'research:{GEN}').decode().strip(),
           'seed_generator_blob': git('rev-parse', f'research:{SEEDGEN}').decode().strip()}
    # 1. parametric seed text reproduces the release text on the release frame
    old = json.loads(git('show', 'research:evidence/joint-fixture10-20261026/JFp_SHA_INPUT.json'))['message']
    assert ndo(seed_text(old)) == git('show', 'research:lean/NDO_JFp_SeedHash.lean').decode(), 'parametric seed generator does not reproduce release'
    rep['seed_text_reproduces_release'] = True
    # 2. SHA generator on the PIN2 frame
    frame = (HERE / 'inputs/transfer-init_frame.bin').read_bytes(); pb = (HERE / 'inputs/transfer-public_bytes.bin').read_bytes()
    assert len(frame) == 1595 and frame[43:43 + 1520] == pb
    root = Path(tempfile.mkdtemp(prefix='pin2w4-sha-')); P = root / 'evidence/joint-fixture10-20261026'; P.mkdir(parents=True)
    (root / 'evidence/joint-fixture6-20261026').mkdir(parents=True); (root / 'lean').mkdir()
    (root / 'lean/JFp_SHA256.lean').write_bytes(git('show', 'research:lean/JFp_SHA256.lean'))
    (root / 'evidence/joint-fixture6-20261026/JFu_SEED_DIAGNOSTIC.json').write_text(json.dumps({'kind': 'PIN2 W4: Python section-9 model (PIN2W4_inputs.py)',
        'domain_hex': frame[:38].hex(), 'semantic_length': len(pb), 'root_hex': frame[-32:].hex(), 'init_input_length': len(frame), 'init_input_sha256': hashlib.sha256(frame).hexdigest()}))
    (root / 'evidence/joint-fixture6-20261026/JFu_SERIALIZATION_DIAGNOSTIC.json').write_text(json.dumps({'semantic_bytes': list(pb)}))
    g = git('show', f'research:{GEN}').decode()
    subs = [('assert len(msg)==1530', 'assert len(msg)==1595'), ('blocks=25)', 'blocks=len(padded)//64)')]
    for a, b in subs: assert g.count(a) == 1, a; g = g.replace(a, b)
    (P / 'JFp_generate_sha.py').write_text(g); (HERE / 'generators/JFp_generate_sha.py').write_text(g)
    rep['sha_generator_substitutions'] = subs
    subprocess.run([sys.executable, '-I', str(P / 'JFp_generate_sha.py')], check=True)
    shain = json.loads((P / 'JFp_SHA_INPUT.json').read_text()); assert shain['message'] == list(frame) and shain['blocks'] == 26
    shutil.copy(P / 'JFp_SHA_INPUT.json', HERE / 'PIN2_JFp_SHA_INPUT.json')
    out = HERE / 'sources'; mods = []
    for f in sorted((root / 'lean').glob('JFp_SHABlock*.lean')):
        t = ndo(f.read_text()); name = 'NDO_' + f.stem; (out / f'{name}.lean').write_text(t)
        try: rel = git('show', f'research:lean/{name}.lean').decode(); ch = rel != t
        except subprocess.CalledProcessError: rel = None; ch = True
        mods.append({'module': name, 'new_module': rel is None, 'text_changed': ch, 'sha256': hashlib.sha256(t.encode()).hexdigest()})
    t = ndo(seed_text(list(frame))); (out / 'NDO_JFp_SeedHash.lean').write_text(t)
    mods.append({'module': 'NDO_JFp_SeedHash', 'new_module': False, 'text_changed': True, 'sha256': hashlib.sha256(t.encode()).hexdigest()})
    final = bytes.fromhex(shain['seed']); assert final == hashlib.sha256(frame).digest()
    rep['modules'] = mods; rep['seed_sha256'] = shain['seed']; rep['seed_bytes'] = list(final)
    (HERE / 'SHA.json').write_text(json.dumps(rep, indent=2) + '\n')
    print(len(mods), 'modules;', 'seed', shain['seed']); shutil.rmtree(root)

if __name__ == '__main__':
    main()
