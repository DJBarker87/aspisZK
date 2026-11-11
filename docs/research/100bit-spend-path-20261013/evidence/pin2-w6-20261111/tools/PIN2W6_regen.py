"""Run an ORIGINAL 26 October fixture generator (verbatim from research, blob
recorded) in a scratch tree, in one of two modes:
  check <gen>  : tree = research sources (26 October values).  The generator
                 must leave every existing file byte-identical (with its own
                 --check flag when it has one).  Any changed file is a failure.
  pin2 <gen>   : tree = PIN2 tree (PIN2W6_tree.py substitutions).  Files the
                 generator changes are its PIN2 outputs; each is compared with
                 the research text and, if changed, written to sources/ under
                 its release name (release import header, NDO_/RPt_/RPu_/RPz8_
                 port changed imports only).
Path.unlink is disabled inside the generator process (no deletion anywhere);
a generator that deletes its intermediate outputs leaves them in the tree.
usage: python3 -I PIN2W6_regen.py check|pin2 <research path of generator> [gen args...]"""
import sys, os, json, hashlib, subprocess, re
from pathlib import Path
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import PIN2W6_src as S
SP = Path('/private/tmp/claude-501/-Users-dominic-ZK/3db59790-41f3-4c53-ae90-3fc42a8cab96/scratchpad')
mode, gen, *gargs = sys.argv[1:]
import PIN2W6_subs as SUB
EV5 = S.EV / 'pin2-w5-20261111'
VALS = json.load(open(EV5 / ('provenance-26oct/DERIVED-26OCT.json' if mode == 'check' else 'PIN2W5_VALUES.json')))
T = SP / ('w6tree-check' if mode == 'check' else 'w6tree-pin2')
W6 = S.W6
sha = lambda b: hashlib.sha256(b).hexdigest()
git = lambda *a: subprocess.run(['git', '-C', str(S.W), *a], capture_output=True, check=True).stdout
blob = git('rev-parse', f'research:{gen}').decode().strip()
src = git('show', f'research:{gen}')
assert (T / gen).read_bytes() == src, 'tree copy of generator differs from research'
# literal substitutions (native values hard-coded in the generator, W5 HARDCODED.json):
# in check mode the substituted text must equal the original (the literal IS the
# 26 October native value); in pin2 mode it carries the PIN2 native value.
code = src.decode()
subs_applied = []
for name, fn in SUB.SUBS.get(gen, []):
    new = fn(code, VALS)
    subs_applied.append(name)
    if mode == 'check': assert new == code, f'substitution {name}: 26 October native values do not reproduce the generator literal'
    code = new
if subs_applied:
    (W6 / 'generators').mkdir(exist_ok=True)
    (W6 / 'generators' / f'{mode}-{Path(gen).name}').write_text(code)
def snap():
    out = {}
    for d in ('lean', 'evidence'):
        for root, _, fs in os.walk(T / d):
            for f in fs:
                p = Path(root) / f; out[str(p.relative_to(T))] = sha(p.read_bytes())
    return out
before = snap()
wrapper = ("import sys, pathlib\npathlib.Path.unlink = lambda self, missing_ok=False: None\n"
           f"sys.argv = [{str(T / gen)!r}] + {gargs!r}\n__file__ = {str(T / gen)!r}\n"
           f"sys.path.insert(0, {str((T / gen).parent)!r})\n"
           f"exec(compile({code!r}, {str(T / gen)!r}, 'exec'))\n")
r = subprocess.run([sys.executable, '-I', '-c', wrapper], cwd=str((T / gen).parent), capture_output=True, text=True)
after = snap()
changed = sorted(k for k in after if k in before and after[k] != before[k])
new = sorted(k for k in after if k not in before)
rep = dict(mode=mode, generator=gen, blob=blob, substitutions=subs_applied, generator_text_sha256=sha(code.encode()), args=gargs, exit=r.returncode, stdout=r.stdout[-2000:], stderr=r.stderr[-3000:], changed=changed, new=new)
if mode == 'check':
    rep['ok'] = r.returncode == 0 and not changed
    print(gen, 'CHECK', 'OK' if rep['ok'] else 'FAIL', 'exit', r.returncode, 'changed', len(changed), 'new', len(new))
else:
    outs = []
    (W6 / 'sources').mkdir(exist_ok=True)
    for k in changed + new:
        if not (k.startswith('lean/') and k.endswith('.lean')): outs.append(dict(file=k, kind='data', sha256=after[k])); continue
        jf = k[5:-5]
        rel = next((c for c in (f'NDO_{jf}', f'RPt_{jf}', f'RPu_{jf}', f'RPz8_{jf}') if S.release(c)[0] is not None), None)
        orig = subprocess.run(['git', '-C', str(S.W), 'show', f'research:{k}'], capture_output=True).stdout
        text = (T / k).read_text()
        row = dict(file=k, jf=jf, release=rel, text_changed_vs_research=sha(text.encode()) != sha(orig), sha256=sha(text.encode()))
        if rel and row['text_changed_vs_research']:
            rb, _ = S.release(rel); rh = [l for l in rb.decode().split('\n') if l.startswith('import ')]
            lines = text.split('\n'); i = 0
            while i < len(lines) and lines[i].startswith('import '): i += 1
            # the release header must be the JF header with names mapped one-to-one
            assert len(rh) == i, (rel, 'import count differs')
            out = '\n'.join(rh + lines[i:])
            (W6 / 'sources' / f'{rel}.lean').write_text(out); row['written'] = f'sources/{rel}.lean'; row['release_sha256'] = sha(out.encode())
        outs.append(row)
    rep['outputs'] = outs
    print(gen, 'PIN2 exit', r.returncode, 'changed', len(changed), 'new', len(new), 'written', sum(1 for o in outs if 'written' in o))
log = W6 / 'REGEN-W6.jsonl'
open(log, 'a').write(json.dumps(rep) + '\n')
if r.returncode: print(r.stderr[-2000:])
