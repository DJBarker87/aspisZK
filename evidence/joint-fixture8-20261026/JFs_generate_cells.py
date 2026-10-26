"""Small exact metadata windows; --check verifies the checked generated sources."""
from pathlib import Path
import re,sys
R=Path(__file__).resolve().parents[2]
raw=(R/'lean/JFx_DataPublic00.lean').read_text();values=[]
for i in range(59):
    line=re.search(r'def c'+f'{i:02}'+r' : List U8 := (.*)',raw).group(1)
    if line.startswith('List.replicate'):
        n,v=re.fullmatch(r'List.replicate (\d+) (\d+)#u8',line).groups()
        values += [v]*int(n)
    else: values += re.findall(r'(\d+)#u8',line)
assert len(values)==1880
base=(R/'lean/JFu_PublicMeta02.lean').read_text()
for k,(off,n) in enumerate([(8,32),(40,32),(72,32),(104,8),(1672,32),(1704,32),(1736,8),(1808,4)]):
    name=f'JFs_Cell{k:02}'
    s=base.replace('JFu_PublicMeta02',name).replace('224',str(off)).replace('256#usize',str(off+n)+'#usize')
    s=re.sub(r'def bytes : List U8 := \[.*?\]', 'def bytes : List U8 := ['+','.join(v+'#u8' for v in values[off:off+n])+']',s)
    s=s.replace('bytes.length=32','bytes.length='+str(n)).replace('.take 32','.take '+str(n)).replace('segment '+str(off)+' 32','segment '+str(off)+' '+str(n))
    s=s.replace(').val=256',').val='+str(off+n))
    s=s.replace('\n#print axioms length',f'\ndef value : Array U8 {n}#usize := ⟨bytes,length⟩\n\n#print axioms length')
    p=R/'lean'/(name+'.lean')
    if '--check' in sys.argv: assert p.read_text()==s,p
    else:p.write_text(s)
print('8 small-window sources match')
