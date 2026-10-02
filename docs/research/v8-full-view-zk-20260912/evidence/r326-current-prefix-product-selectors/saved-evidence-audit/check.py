from pathlib import Path
import hashlib, json, re, subprocess
repo = Path('/Users/dominic/ZK/.worktrees/ZK-v8-r21-public-arithmetic-20260922')
base = repo / 'docs/research/v8-full-view-zk-20260912'
bundle = base / 'evidence/r326-current-prefix-product-selectors'
target = base / 'lean/AspisV8R19/R326PrefixProductSelectors.lean'
manifest = json.loads((bundle / 'manifest.json').read_text())
sums = json.loads((bundle / 'SHA256SUMS.json').read_text())
hashes = {rel: hashlib.sha256((bundle / rel).read_bytes()).hexdigest() == digest for rel, digest in sums.items()}
source = target.read_text()
log = (bundle / manifest['log']).read_text()
names = ['prefixAccum_shift', 'prefixValues_getElem?', 'actual_output_selector']
reports = []
for name in names:
    match = re.search(r"'AspisV8R19\.R326PrefixProductSelectors\." + re.escape(name) + r"' depends on axioms: \[(.*?)\]", log, re.S)
    reports.append((name, [x.strip() for x in match.group(1).replace('\n', ' ').split(',')] if match else None))
assert all(hashes.values())
assert target.read_bytes() == (bundle / 'source/R326PrefixProductSelectors.lean').read_bytes()
assert hashlib.sha256(target.read_bytes()).hexdigest() == manifest['source_sha256']
assert subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=repo, text=True).strip() == manifest['source_revision']
assert all(ax == ['propext', 'Classical.choice', 'Quot.sound'] for _, ax in reports)
assert 'hout : out.val = px.val ++ prefixValues f i n p' in source and '(hj : j < n)' in source
assert 'Zero products are allowed.' in (base / 'R326_CURRENT_PREFIX_PRODUCT_SELECTORS.md').read_text()
print('PASS', len(hashes), 'bundle hash entries;', len(reports), 'axiom reports')
