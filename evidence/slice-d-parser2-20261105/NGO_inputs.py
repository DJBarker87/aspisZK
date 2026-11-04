"""Reconstruct scratch harness inputs from the committed patch and frozen git objects."""
from pathlib import Path
import subprocess,re,difflib
E=Path(__file__).resolve().parent
F='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387'
def original(name):
 r=subprocess.run(['git','show',F+':'+name],capture_output=True,text=True)
 return r.stdout if r.returncode==0 else ''
def load():
 lines=(E/'NGO_harness.patch').read_text().splitlines(True);i=0;out={}
 while i<len(lines):
  assert lines[i].startswith('--- ');i+=1
  assert lines[i].startswith('+++ b/');name=lines[i][6:].strip();i+=1
  old=original(name).splitlines(True);new=[];cursor=0
  while i<len(lines) and not lines[i].startswith('--- '):
   m=re.match(r'@@ -(\d+)(?:,(\d+))? \+(\d+)(?:,(\d+))? @@',lines[i]);assert m,lines[i]
   start=max(0,int(m[1])-1);assert start>=cursor
   new+=old[cursor:start];cursor=start;i+=1
   while i<len(lines) and not lines[i].startswith(('@@ ','--- ')):
    line=lines[i];i+=1
    if line.startswith('\\'):continue
    assert line[:1] in [' ','-','+'],line
    if line[0] in [' ','-']:
     assert cursor<len(old) and old[cursor]==line[1:],(name,cursor)
     cursor+=1
    if line[0] in [' ','+']:new.append(line[1:])
  new+=old[cursor:];out[name]=''.join(new)
 return out
def write(inputs):
 patch=[]
 for name,text in inputs.items():
  old=original(name)
  patch+=difflib.unified_diff(old.splitlines(True),text.splitlines(True),fromfile='a/'+name if old else '/dev/null',tofile='b/'+name)
 (E/'NGO_harness.patch').write_text(''.join(patch))
