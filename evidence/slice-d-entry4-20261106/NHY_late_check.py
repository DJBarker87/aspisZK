"""Validate late native support without promoting an incomplete parent row."""
from pathlib import Path
import json,lzma,re,hashlib,subprocess
E=Path(__file__).resolve().parent
read=lambda p:json.loads(p.read_text())
def log(a):return lzma.decompress((E/a/'stdout.log.xz').read_bytes()).decode()
pairs=[(69,70),(71,72),(73,74),(75,76),(77,78),(79,80),(81,82),(83,84),(85,86),(87,88),(62,89),(90,91),(95,96),(97,98),(99,100),(101,102),(104,105),(106,107),(108,109),(111,112),(114,115),(116,117),(119,120)]
results=[]
for p,n in pairs:
 pa,na=f'NHY_K{p:03}',f'NHY_K{n:03}';rp,rn=read(E/pa/'receipt.json'),read(E/na/'receipt.json')
 assert rp['exit_status']==0 and 'VERIFICATION:- SUCCESSFUL' in log(pa)
 s=log(na);assert rn['exit_status']==1 and re.search(r'\*\* 1 of \d+ failed',s) and 'Failed Checks:' in s and 'timed out' not in s
 cp,cn=rp['native_command'],rn['native_command'];assert cp[cp.index('--features')+1]==cn[cn.index('--features')+1]
 results.append(dict(positive=pa,negative=na,status='PASS_PAIRED_SUPPORT',promotes_parent=False))
for k in [68,92,103,113,118]:assert 'timed out' in log(f'NHY_K{k:03}')
assert 'Failed to match the following harness' in log('NHY_K110')
assert read(E/'NHY_CLOSED.json')['new_composed_rows']==14
def code_only(text):
 # Lean nested comments and strings are not declarations or proof terms.
 out=[];i=0;depth=0;string=False
 while i<len(text):
  if depth:
   if text.startswith('/-',i):depth+=1;i+=2
   elif text.startswith('-/',i):depth-=1;i+=2
   else:i+=1
  elif string:
   if text[i]=='\\':i+=2
   elif text[i]=='"':string=False;i+=1
   else:i+=1
  elif text.startswith('/-',i):depth=1;i+=2
  elif text.startswith('--',i):
   j=text.find('\n',i);i=len(text) if j<0 else j;out.append('\n')
  elif text[i]=='"':string=True;i+=1
  else:out.append(text[i]);i+=1
 assert depth==0 and not string
 return ''.join(out)
for p in E.glob('NHY_*.lean'):
 s=code_only(p.read_text());assert not re.search(r'\b(?:sorry|admit|axiom|native_decide)\b',s),p
 # New prefix proofs do not raise kernel/resource limits.
 assert not re.search(r'^set_option (?:maxRecDepth|maxHeartbeats|synthInstance.maxHeartbeats)',s,re.M),p
out=dict(status='PASS_SUPPORT_ONLY',pairs=results,closed_rows_unchanged=14,whole_tx1_entry='OPEN',whole_tx2_entry='OPEN',quarantine='Debug log sink is not proof of deployed String writer. No formatter/error row credit. Capacity metadata does not execute a callback and is not formatter realization.',timeouts_excluded=['NHY_K068','NHY_K092','NHY_K103','NHY_K113','NHY_K118'],source_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),source_revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip())
(E/'NHY_LATE_SUPPORT.json').write_text(json.dumps(out,indent=1)+'\n');print(json.dumps(dict(status=out['status'],pairs=len(results))))
