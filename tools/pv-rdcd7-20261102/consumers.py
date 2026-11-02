"""Read-only git-grep census at pinned local and remote refs, plus import consumers."""
from pathlib import Path
import subprocess,json,hashlib,re
R=Path(__file__).resolve().parents[2]; E=R/'evidence/pv-rdcd7-20261102'
def git(*a):return subprocess.check_output(['git',*a],cwd=R)
refs=[x.split() for x in (E/'REFS-before.txt').read_text().splitlines()]
head=git('rev-parse','HEAD').decode().strip();refs.append(['HEAD',head])
byrev={}
for ref,rev in refs:byrev.setdefault(rev,[]).append(ref)
results=[]
for rev,names in byrev.items():
 q=subprocess.run(['git','grep','-n','-I','-E','PV_RDCD4_(BytesSource|SliceRange194)',rev,'--','*.lean','*.py','*.sh','*.rs'],cwd=R,capture_output=True)
 assert q.returncode in (0,1),(names,q.stderr)
 hits=q.stdout.decode();(E/('grep-'+rev+'.txt')).write_text(hits)
 # Scan Lean imports mechanically, closing reverse edges from both corrected roots.
 q=subprocess.run(['git','grep','-n','-E','^import R1Z\\.PV_',rev,'--','*.lean'],cwd=R,capture_output=True)
 assert q.returncode in (0,1)
 edges={}
 for line in q.stdout.decode().splitlines():
  path,ln,body=line[len(rev)+1:].split(':',2)
  mod='R1Z.'+Path(path).stem if '/R1Z/' in path else None
  if mod:edges.setdefault(mod,set()).update(re.findall(r'R1Z\.[A-Za-z0-9_]+',body))
 cone={'R1Z.PV_RDCD4_BytesSource','R1Z.PV_RDCD4_SliceRange194'};changed=True
 while changed:
  old=len(cone);cone|={m for m,deps in edges.items() if deps&cone};changed=len(cone)>old
 results.append(dict(revision=rev,refs=names,grep_file='grep-'+rev+'.txt',grep_sha256=hashlib.sha256(hits.encode()).hexdigest(),reverse_import_cone=sorted(cone),lean_direct_files=sorted({line[len(rev)+1:].split(':',1)[0] for line in hits.splitlines() if '.lean:' in line})))
(E/'CONSUMERS-census.json').write_text(json.dumps(dict(command='git grep -n -I -E PV_RDCD4_(BytesSource|SliceRange194) REV -- *.lean *.py *.sh *.rs',refs_count=len(refs),unique_revisions=len(byrev),results=results),indent=2)+'\n')
print('Refs',len(refs),'revisions',len(byrev))
for x in results:
 if x['lean_direct_files']:print(','.join(x['refs']),len(x['lean_direct_files']),len(x['reverse_import_cone']))
