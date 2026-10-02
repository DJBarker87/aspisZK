from pathlib import Path
import hashlib,json,re,subprocess
repo=Path('/Users/dominic/ZK/.worktrees/ZK-v8-r21-public-arithmetic-20260922'); base=repo/'docs/research/v8-full-view-zk-20260912'; b=base/'evidence/r337-current-initialized-reverse-execution'; t=base/'lean/AspisV8R19/R337InitializedReverseExecution.lean'; m=json.loads((b/'manifest.json').read_text())
assert all(hashlib.sha256((b/r).read_bytes()).hexdigest()==h for r,h in json.loads((b/'SHA256SUMS.json').read_text()).items())
assert t.read_bytes()==(b/'source/R337InitializedReverseExecution.lean').read_bytes()
assert hashlib.sha256(t.read_bytes()).hexdigest()==m['source_sha256']=='fe9cb5167e48b93eb2ed58b7a084f958e2662b69831d55f96776176b2bb4fc08'
head=subprocess.check_output(['git','rev-parse','HEAD'],cwd=repo,text=True).strip()
assert m['source_revision']=='37d5dd7ecb2c6f7b98822147522b043884ef77d9' and subprocess.run(['git','merge-base','--is-ancestor',m['source_revision'],head],cwd=repo).returncode==0
assert hashlib.sha256((base/'lean/AspisR335PrefixPairInverseRaw.lean').read_bytes()).hexdigest()==m['compile_dependency_status']['dependency_sha256']['AspisR335PrefixPairInverseRaw.lean']
assert hashlib.sha256((base/'lean/AspisV8R19/R336PrefixPairInverseExecution.lean').read_bytes()).hexdigest()==m['compile_dependency_status']['dependency_sha256']['AspisV8R19/R336PrefixPairInverseExecution.lean']
log=(b/m['log']).read_text(); assert m['exit_status']==0 and m['wall_time']=='0:01.71' and m['peak_rss_kib']==3719608 and m['swaps']==0 and 'Exit status: 0' in log and 'Swaps: 0' in log
assert ' '.join((b/'axioms.txt').read_text().split())==' '.join('\n'.join(re.findall(r"'[^']+' depends on axioms: \[.*?\]",log,re.S)).split())
for n in ['first_prefix_initialized_reverse','second_prefix_initialized_reverse']:
 q=re.search(re.escape("'AspisV8R19.R337InitializedReverseExecution."+n+"' depends on axioms: [")+r"(.*?)\]",log,re.S); assert q and {x.strip() for x in q.group(1).replace('\n',' ').split(',')}=={'propext','Classical.choice','Quot.sound'}
print('PASS R337 saved-evidence audit')
