from pathlib import Path
import hashlib,json,re,subprocess
repo=Path('/Users/dominic/ZK/.worktrees/ZK-v8-r21-public-arithmetic-20260922'); base=repo/'docs/research/v8-full-view-zk-20260912'; b=base/'evidence/r341-current-prefix-nonzero'; t=base/'lean/AspisV8R19/R341PrefixNonzero.lean'; m=json.loads((b/'manifest.json').read_text())
assert all(hashlib.sha256((b/r).read_bytes()).hexdigest()==h for r,h in json.loads((b/'SHA256SUMS.json').read_text()).items())
assert t.read_bytes()==(b/'source/R341PrefixNonzero.lean').read_bytes()
assert hashlib.sha256(t.read_bytes()).hexdigest()==m['source_sha256']=='6e94af41b981bf55b986756729ff7c3c0624c997a0347918711ac2d74aab95b4'
head=subprocess.check_output(['git','rev-parse','HEAD'],cwd=repo,text=True).strip(); assert subprocess.run(['git','merge-base','--is-ancestor',m['source_revision'],head],cwd=repo).returncode==0
log=(b/m['log']).read_text(); assert m['exit_status']==0 and m['wall_time']=='0:01.57' and m['peak_rss_kib']==3710056 and m['swaps']==0
assert ' '.join((b/'axioms.txt').read_text().split())==' '.join('\n'.join(re.findall(r"'[^']+' depends on axioms: \[.*?\]",log,re.S)).split())
s=t.read_text()
for n in ['sourcePrefixValue_succ','sourcePrefixValue_ne_zero_iff','initialized_pair_total_ne_zero_iff']:
 q=re.search(re.escape("'AspisV8R19.R341PrefixNonzero."+n+"' depends on axioms: [")+r"(.*?)\]",log,re.S); assert q and {x.strip() for x in q.group(1).replace('\n',' ').split(',')}=={'propext','Classical.choice','Quot.sound'}
 h=s.split('theorem '+n,1)[1].split(':= by',1)[0]
 assert all(x not in h for x in ['Slice','Iter','Result','guard'])
print('PASS R341 saved-evidence audit')
