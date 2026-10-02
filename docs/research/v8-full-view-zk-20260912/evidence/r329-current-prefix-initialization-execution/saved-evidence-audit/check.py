from pathlib import Path
import hashlib, json, re, subprocess
repo = Path('/Users/dominic/ZK/.worktrees/ZK-v8-r21-public-arithmetic-20260922')
base = repo / 'docs/research/v8-full-view-zk-20260912'
items = [
 ('r328-current-prefix-initialization-raw','lean/AspisR328PrefixInitializationRaw.lean','429e49ca420e8a65d6791c3d02413811e010c296e6d6de05c049e32fac5f9e49',['AspisR328PrefixInitializationRaw.selectedPrefix0']),
 ('r329-current-prefix-initialization-execution','lean/AspisV8R19/R329PrefixInitializationExecution.lean','69c73c8c669ca59a9f3bf846ce919f44ecd822228f0649e6fd59b118ad03046a',['AspisV8R19.R329PrefixInitializationExecution.selectedPrefix0_empty','AspisV8R19.R329PrefixInitializationExecution.selectedPrefix0_products'])]
for key, target_rel, sha, names in items:
 b=base/'evidence'/key; m=json.loads((b/'manifest.json').read_text()); target=base/target_rel
 assert all(hashlib.sha256((b/r).read_bytes()).hexdigest()==d for r,d in json.loads((b/'SHA256SUMS.json').read_text()).items())
 assert target.read_bytes()==(b/'source'/target.name).read_bytes() and hashlib.sha256(target.read_bytes()).hexdigest()==sha==m['source_sha256']
 assert subprocess.check_output(['git','rev-parse','HEAD'],cwd=repo,text=True).strip()==m['source_revision']
 log=(b/m['log']).read_text(); axiom_file=' '.join((b/'axioms.txt').read_text().split()); report=' '.join('\n'.join(re.findall(r"'[^']+' depends on axioms: \[.*?\]",log,re.S)).split())
 assert axiom_file==report
 for name in names:
  match=re.search(re.escape("'"+name+"' depends on axioms: [")+r"(.*?)\]",log,re.S)
  assert match and set(x.strip() for x in match.group(1).replace('\n',' ').split(','))=={'propext','Classical.choice','Quot.sound'}
 assert m['exit_status']==0 and m['swaps']==0
 print('PASS',key,len(names),'axiom reports')
