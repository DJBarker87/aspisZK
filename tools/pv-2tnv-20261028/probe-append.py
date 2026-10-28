"""Small arithmetic preflight only; Lean certificates remain the proof gate."""
from pathlib import Path
import re,json
R=Path(__file__).resolve().parents[2];E=R/'evidence/pv-2tnv-20261028/resume';P=2147483647
c=(R/'docs/research/v8-r0-sem-proof-20261008/lean/R0P/PoseidonConstants.lean').read_text()
def nums(s):return [int(t,0) for t in re.findall(r'0x[0-9a-f]+|(?<![A-Za-z])\d+',s)]
def constant(name,nextname):return nums(c.split('def '+name)[1].split(':=',1)[1].split('/--',1)[0])
ei=constant('poseidonExternalInitial','');ef=constant('poseidonExternalFinal','');ic=constant('poseidonInternalConstants','');sh=constant('poseidonInternalShifts','');assert len(ei)==64 and len(ef)==64 and len(ic)==14 and len(sh)==15,(len(ei),len(ef),len(ic),len(sh))
def linear(s):
 local=[]
 for g in range(4):
  a,b,d,e=s[4*g:4*g+4];t01=a+b;t23=d+e;total=t01+t23;t1=total+b;t3=total+e
  local += [(t1+t01)%P,(t1+2*d)%P,(t3+t23)%P,(t3+2*a)%P]
 sums=[sum(local[i::4]) for i in range(4)]
 return [(v+sums[i%4])%P for i,v in enumerate(local)]
def perm(s):
 states=[s[:]];s=linear(s);states.append(s)
 for k in range(4):s=linear([pow((v+ei[k*16+i])%P,5,P) for i,v in enumerate(s)]);states.append(s)
 for k in range(14):
  t=s[:];t[0]=pow((t[0]+ic[k])%P,5,P);part=sum(t[1:]);total=part+t[0];s=[(part-t[0])%P]+[(total+t[i]*(1<<sh[i-1]))%P for i in range(1,16)];states.append(s)
 for k in range(4):s=linear([pow((v+ef[k*16+i])%P,5,P) for i,v in enumerate(s)]);states.append(s)
 return states

def node(l,r):return perm(l+r[:7]+[(r[7]-1051521018)%P])
def readbytes():
 s=(E/'JFx_DataPublic00.lean.txt').read_text();b=[]
 for line in s.splitlines():
  if re.match('def c[0-9]',line):
   if 'replicate' in line:
    n,v=map(int,re.search(r'replicate (\d+) (\d+)#u8',line).groups());b.extend([v]*n)
   else:b.extend(map(int,re.findall(r'(\d+)#u8',line)))
 return bytes(b)
b=readbytes();dig=lambda off:[int.from_bytes(b[j:j+4],'little') for j in range(off,off+32,4)]
# Existing pinned frozen roots are in the runjoin mathematical table.
table=(R/'docs/research/v8-r0-zk-20261009/lean/R1Z/PV_RunJoin_RootModelTable.lean').read_text()
raw=table.split('def literal',1)[1].split(':=',1)[1].split('theorem',1)[0]
roots=[list(map(int,re.findall(r'\d+',v))) for v in re.findall(r'!\[([^\[\]]+)\]',raw)];assert len(roots)==21
pair=node(dig(1816),dig(1848));cur=pair[-1][:8];cells=[pair]
for k in range(20):
 left,right=(dig(336+32*k),cur) if (13>>k)&1 else (cur,roots[k])
 states=node(left,right);cells.append(states);cur=states[-1][:8]
expected=dig(992);carry=cells[1][-1][:8]
result=dict(output_pair=pair[-1][:8],root=cur,expected_root=expected,root_matches=cur==expected,carry=carry,expected_carry=dig(1056),carry_matches=carry==dig(1056),cells=cells)
(E/'append-probe.json').write_text(json.dumps(result,indent=2)+'\n')
print({k:v for k,v in result.items() if k!='cells'})
