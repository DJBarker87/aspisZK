import hashlib, json, re, subprocess
from pathlib import Path

work = Path(__file__).resolve().parent.parent
local = Path(__file__).resolve().parent
old = Path('/Users/dominic/.cache/aspis/r1-j1-r7-r8-local-check-20261015-7c5ca8699')
merge = Path('/Users/dominic/ZK/.worktrees/r1-j1-r11-r12-20261015/.j1-merge-check')
mapping = json.loads((old/'current-closure.json').read_text())
mapping.update(json.loads((merge/'worker-b-merged-closure.json').read_text())['project_modules'])
for name, path in list(mapping.items()):
    if path.startswith('/') and '/docs/' in path:
        mapping[name] = 'docs/' + path.split('/docs/', 1)[1]
for path in (work/'docs/research/100bit-spend-path-20261013/lean').glob('*.lean'):
    mapping['R1'+path.stem] = str(path.relative_to(work))
files = subprocess.check_output(['rg', '--files', 'docs/research', 'AspisFormal'], cwd=work, text=True).splitlines()

def resolve(name):
    path = mapping.get(name)
    if path and (work/path).exists():
        return path
    suffix = name.replace('.', '/') + '.lean'
    matches = [p for p in files if '/evidence/' not in p and p.endswith('/'+suffix)]
    return matches[0] if len(matches) == 1 else None

modules, missing, unresolved = {}, [], []
def visit(name):
    if name in modules or name.split('.')[0] in {'Mathlib', 'Lean', 'Init', 'Std', 'Batteries', 'Qq', 'Aesop', 'Plausible', 'ProofWidgets', 'ImportGraph', 'LeanSearchClient', 'Cli'}:
        return
    path = resolve(name)
    if not path:
        unresolved.append(name)
        return
    source = (work/path).read_bytes()
    record = {'source': path, 'source_sha256': hashlib.sha256(source).hexdigest()}
    modules[name] = record
    if name != 'R1SemanticPrefixAgreement':
        relative = Path(*name.split('.')).with_suffix('.olean')
        cache = next((c for c in (old, merge) if (c/'objects'/relative).exists()), None)
        if cache:
            obj = cache/'objects'/relative
            ref = '7c5ca8699' if cache == old else '185d576e5e7f2e2aee01db7ddb1d74b09d77cc6a'
            historical = subprocess.run(['git', 'show', ref+':'+path], cwd=work, stdout=subprocess.PIPE, stderr=subprocess.DEVNULL)
            record.update(object=str(obj), object_sha256=hashlib.sha256(obj.read_bytes()).hexdigest(), source_cache_comparison_revision=ref, exact_source_match_to_cache_revision=historical.returncode == 0 and historical.stdout == source)
        else:
            missing.append(name)
    for line in re.findall(r'^import\s+([^\n]+)', source.decode(), re.M):
        for imp in line.split():
            if re.fullmatch(r'[A-Z][A-Za-z0-9_.]*', imp):
                visit(imp)

visit('R1SemanticPrefixAgreement')
report = {'base': subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=work, text=True).strip(), 'modules': modules, 'missing_objects': missing, 'unresolved': unresolved}
(local/'import-source-pins.json').write_text(json.dumps(report, indent=2)+'\n')
print(json.dumps({'module_count': len(modules), 'missing': missing, 'unresolved': unresolved, 'source_mismatches': [m for m, r in modules.items() if r.get('exact_source_match_to_cache_revision') is False]}, indent=2))
