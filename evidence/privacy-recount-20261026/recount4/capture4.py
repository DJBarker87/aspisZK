from pathlib import Path
import subprocess,json,re,hashlib
P=Path(__file__).resolve().parent
refs={'research':'research','rw':'codex/cx-prover-rw-20261023','cb':'codex/pv-cb-20261026','cb3':'codex/pv-cb3-20261026','cbmid':'codex/pv-cbmid-20261027','cblib':'codex/pv-cblib-20261027','extract':'codex/pv-extract-20261027','op223':'codex/pv-op223-20261027','join':'codex/pv-join-20261026','runjoin':'codex/pv-runjoin-20261026','optb':'codex/pv-optb-20261027'}
def git(*args):return subprocess.check_output(['git',*args])
pins={k:git('rev-parse',r).decode().strip() for k,r in refs.items()}
(P/'pins.json').write_text(json.dumps({'branches':refs,'revisions':pins,'worktree_base':git('rev-parse','HEAD').decode().strip(),'cblib2':'no separate branch; continuation is on cblib, RESUME.md and OPS.md audited'},indent=2)+'\n')
manifest=[];trees={}
for k,rev in pins.items():
 trees[k]={}
 for l in git('ls-tree','-r',rev).decode().splitlines():
  meta,path=l.split('\t');trees[k][path]=meta.split()[2]
 def selected(path):
  if path.endswith('.lean') and '/lean/' in path and ('/R1Z/' in path or 'prover-rw-20261023/' in path):return True
  if path.endswith('.md') and path.startswith(('evidence/pv-cblib-','evidence/pv-extract-','evidence/pv-op223-','evidence/pv-optb-','evidence/pv-runjoin1','evidence/pv-inv','evidence/pv-srcid3-')):return True
  if path.endswith('.md') and path in ['evidence/pv-cb-20261026/RESUME-SOURCE-ROWS.md','evidence/pv-cb3-20261026/HANDOFF.md','evidence/pv-join-20261026/wire/IMPORT-CHAIN.md']:return True
  return path in ['evidence/pv-join-20261026/wire/import-chain.json','design/RELEASE-LEDGER-20261025.md','design/PRIVACY-LEDGER-20261026.md','docs/research/v8-r0-zk-20261009/LOG.md']
 for path,blob in trees[k].items():
  if not selected(path):continue
  # Content-addressed snapshots avoid copying identical files between branches.
  raw=git('cat-file','blob',blob);sha=hashlib.sha256(raw).hexdigest();out=P/'objects'/(blob+'.txt')
  if not out.exists():out.parent.mkdir(exist_ok=True);out.write_bytes(raw)
  manifest.append(dict(ref=k,revision=rev,path=path,blob=blob,sha256=sha,snapshot=str(out.relative_to(P))))
(P/'manifest.json').write_text(json.dumps(manifest,indent=2)+'\n')
rows=json.loads((P.parent/'recount3/rows3.json').read_text());audit=[]
for r in rows:
 path,_,decl=r.get('definition','').partition('#');found=[]
 for k,tree in trees.items():
  if path in tree:
   raw=git('cat-file','blob',tree[path]);found.append(dict(ref=k,path=path,blob=tree[path],sha256=hashlib.sha256(raw).hexdigest(),declaration=decl))
 audit.append(dict(id=r['id'],definition=r.get('definition'),sources=found,unchanged_research_definition=bool(path and trees['research'].get(path)==subprocess.run(['git','rev-parse',pins['research']+':'+path],capture_output=True,text=True).stdout.strip())))
(P/'definition-audit4.json').write_text(json.dumps(audit,indent=2)+'\n')
print('Pinned',len(pins),'branches;',len(manifest),'source records;',len(audit),'row definitions;',len(list((P/'objects').iterdir())),'unique objects')
