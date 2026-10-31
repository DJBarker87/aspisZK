"""Strict, context-exact unified patch replay in memory; never executes a patch."""
import re,subprocess
F='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387'
def replay(raw,repo):
 lines=raw.splitlines(keepends=True);i=0;out={}
 while i<len(lines):
  assert lines[i].startswith('--- ');oldpath=lines[i][4:].strip();newpath=lines[i+1][4:].strip();i+=2
  assert newpath.startswith('b/') and '..' not in newpath.split('/')
  path=newpath[2:]
  if oldpath=='/dev/null':old=[]
  else:
   assert oldpath=='a/'+path
   old=subprocess.check_output(['git','show',F+':'+path],cwd=repo).decode().splitlines(keepends=True)
  result=[];pos=0
  while i<len(lines) and lines[i].startswith('@@ '):
   h=re.match(r'@@ -(\d+)(?:,(\d+))? \+(\d+)(?:,(\d+))? @@',lines[i]);assert h
   start=int(h[1]);oc=int(h[2] or '1');nc=int(h[4] or '1');target=0 if start==0 else start-1
   assert target>=pos
   result.extend(old[pos:target]);pos=target;i+=1;seenold=seennew=0
   while i<len(lines) and lines[i][:1] in [' ','-','+'] and not lines[i].startswith('--- '):
    line=lines[i];i+=1
    if line[0] in ' -':assert old[pos]==line[1:],(path,pos);pos+=1;seenold+=1
    if line[0] in ' +':result.append(line[1:]);seennew+=1
   assert seenold==oc and seennew==nc,(path,seenold,oc,seennew,nc)
  result.extend(old[pos:]);out[path]=''.join(result).encode()
 return out
