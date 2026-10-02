from pathlib import Path
import hashlib, json, re, subprocess
repo=Path('/Users/dominic/ZK/.worktrees/ZK-v8-r21-public-arithmetic-20260922')
base=repo/'docs/research/v8-full-view-zk-20260912'; b=base/'evidence/r332-current-prefix-initialization-selectors'
target=base/'lean/AspisV8R19/R332PrefixInitializationSelectors.lean'; m=json.loads((b/'manifest.json').read_text())
assert all(hashlib.sha256((b/r).read_bytes()).hexdigest()==h for r,h in json.loads((b/'SHA256SUMS.json').read_text()).items())
assert target.read_bytes()==(b/'source/R332PrefixInitializationSelectors.lean').read_bytes()
assert hashlib.sha256(target.read_bytes()).hexdigest()==m['source_sha256']=='ca9142ca2a55ef8bfd13d2b78ad1a0ba9aff45f28c844839493233b88ddf5517'
assert subprocess.check_output(['git','rev-parse','HEAD'],cwd=repo,text=True).strip()==m['source_revision']=='86706bd4cc5aa6d51cf36828d6c049af8202a403'
log=(b/m['log']).read_text(); ax=' '.join((b/'axioms.txt').read_text().split())
assert ax==' '.join('\n'.join(re.findall(r"'[^']+' depends on axioms: \[.*?\]",log,re.S)).split())
for n in ['selected_prefix_output_length','selected_prefix_output_reads','selected_prefix_output_last','selected_prefix_initialization_bundle','selected_prefix_actual_last']:
 m_axiom=re.search(re.escape("'AspisV8R19.R332PrefixInitializationSelectors."+n+"' depends on axioms: [")+r"(.*?)\]",log,re.S)
 assert m_axiom and {x.strip() for x in m_axiom.group(1).replace('\n',' ').split(',')}=={'propext','Classical.choice','Quot.sound'}
print('PASS R332 saved-evidence audit')
