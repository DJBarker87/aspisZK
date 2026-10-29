"""Reconstruct own scratch inputs from frozen blobs and committed unified patches."""
from pathlib import Path
import re,subprocess,json,sys
E=Path(__file__).resolve().parent
REV='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387'
def parse_patch(p,base):
 lines=p.read_text().splitlines(True);i=0;out={}
 while i<len(lines):
  assert lines[i].startswith('--- '),(i,lines[i]);oldname=lines[i][4:].strip();i+=1
  assert lines[i].startswith('+++ ');name=lines[i][4:].strip().removeprefix('b/');i+=1
  old=[] if oldname=='/dev/null' else base(name).splitlines(True);cursor=0;buf=[]
  while i<len(lines) and lines[i].startswith('@@ '):
   m=re.match(r'@@ -(\d+)(?:,(\d+))? \+(\d+)(?:,(\d+))? @@',lines[i]);assert m
   start=int(m[1]);start=start-1 if start else 0
   buf+=old[cursor:start];cursor=start;i+=1
   while i<len(lines) and not lines[i].startswith(('@@ ','--- ')):
    l=lines[i];i+=1
    if l.startswith('\\'):continue
    assert l[:1] in [' ','-','+'],repr(l)
    if l[:1] in [' ','-']:
     assert cursor<len(old) and old[cursor]==l[1:],(name,cursor)
     cursor+=1
    if l[:1] in [' ','+']:buf.append(l[1:])
  buf+=old[cursor:];out[name]=''.join(buf)
 return out

def frozen(n):return subprocess.check_output(['git','show',REV+':'+n],text=True)
def native(p=None):return parse_patch(Path(p) if p else E/'NEA_native.patch',frozen)
def references():
 for n,s in parse_patch(E/'NEA_REFERENCE_INPUTS.patch',lambda _: '').items():
  (E/(Path(n).name+'.txt')).write_text(s)
if __name__=='__main__':
 a=sys.argv[1] if len(sys.argv)>1 else None
 patch=E/a/'NEA_harness.patch' if a else E/'NEA_native.patch'
 (E/'NEA_PAYLOAD.json').write_text(json.dumps(native(patch)))
 references();print('Restored scratch inputs from',patch)
