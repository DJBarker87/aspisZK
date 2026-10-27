"""Resolve newly discovered exact hashes against historical Lean source blobs."""
from pathlib import Path
import json,subprocess,hashlib,time
O=Path(__file__).parent;d=json.load(open(O/'EJS_recursive-frontier.json'));wanted={r['sha256'] for r in d['blocked'].values() if r['reason'] in ('attested hash not found in git','attested hash not resolved by HEAD/retained index')};initial=set(wanted);found=json.loads((O/'EJS_recursive-history-resolution.json').read_text()).get('found',{}) if (O/'EJS_recursive-history-resolution.json').exists() else {};start=time.monotonic()
proc=subprocess.Popen(['git','cat-file','--batch'],stdin=subprocess.PIPE,stdout=subprocess.PIPE);seen=set();count=0;total=0
for line in subprocess.check_output(['git','rev-list','--objects','--all'],text=True).splitlines():
 oid,_,path=line.partition(' ')
 if not path.endswith(('.lean','.lean.txt')) or oid in seen:continue
 seen.add(oid);proc.stdin.write((oid+'\n').encode());proc.stdin.flush();head=proc.stdout.readline().split()
 if len(head)!=3 or head[1]!=b'blob':
  if len(head)==3:proc.stdout.read(int(head[2])+1)
  continue
 n=int(head[2]);b=proc.stdout.read(n);proc.stdout.read(1);h=hashlib.sha256(b).hexdigest();count+=1;total+=n
 if h in wanted:
  revisions=subprocess.check_output(['git','log','--all','--format=%H','--find-object='+oid,'--',path],text=True).splitlines();found[h]=dict(blob=oid,path=path,revision=revisions[0] if revisions else 'git blob exists; revision unlocated',bytes=n);wanted.remove(h);print('found',h,path,flush=True)
 if not wanted:break
proc.terminate();report=dict(requested=sorted(initial),found=found,not_resolved_by_history_scan=sorted(wanted),blobs_checked=count,bytes_checked=total,wall_seconds=time.monotonic()-start,scope='Historical .lean/.lean.txt blobs, filtering names after full object traversal; this is not an exhaustive all-object absence proof. Original 19 selected and 329 historical failures remain unchanged.')
(O/'EJS_recursive-history-resolution.json').write_text(json.dumps(report,indent=2)+'\n');print('history',count,'blobs','resolved',len(found),'remaining',len(wanted),flush=True)
