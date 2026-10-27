from pathlib import Path
import re,json,sys,runpy
P=Path(__file__).resolve().parent;R=P.parents[1]
g=runpy.run_path(str(P/'JGn_generate_copy_numeric.py'));add=g['add'];mul=g['mul'];Z=g['Z'];literal=g['literal'];M=g['M'];cells=g['cells']
def sub(x,y):return tuple((a-b)%M for a,b in zip(x,y))
def poww(x,n):
 out=(1,0,0,0)
 for _ in range(n):out=mul(out,x)
 return out
def low(v,t):
 out=Z
 for x in reversed(v):out=add(x,mul(t,out))
 return out
src=(R/'lean/JFm_Coordinates.lean').read_text()
coords=[tuple(map(int,re.findall(r'(\d+)#u32',src.split(f'def value{i:02} :')[1].split('\n')[0]))) for i in range(25)]
t=coords[2];mu=coords[13];one=(1,0,0,0);sem=cells('semantic');pos=cells('poseidon');copy=cells('copy');helper=(1520023580,1972807226,213458520,1570606483)
data={'theta4':poww(t,4),'theta28':poww(t,28),'sem16':low(sem[16:],t),'sem08':low(sem[8:],t),'sem00':low(sem,t),'pos':low(pos,t)}
eq=one
for j in reversed(range(10)):
 x=coords[3+j];y=coords[15+j]
 eq=mul(add(mul(x,y),mul(sub(one,x),sub(one,y))),eq)
 if j==5:data['eq05']=eq
data['eq00']=eq
data['comp']=add(add(mul(data['theta28'],copy[0]),mul(data['theta4'],data['sem00'])),data['pos'])
terminal=add(add(mul(eq,data['comp']),mul(mu,helper)),mul(mul(poww(mu,2),sub(one,copy[1])),helper))
assert terminal==(1711374173,2026192144,428817833,318295749),terminal
s='''import JGn_CopyNumeric
import FIv_CompositionValue
import FIv_TerminalValue
set_option autoImplicit false
namespace AspisR1.JGn_TerminalData
open Aeneas Aeneas.Std FIq_Native
'''
for n,v in data.items():s+=f'def {n} : field.QM31 := {literal(v)}\n'
s+='end AspisR1.JGn_TerminalData\n'
p=R/'lean/JGn_TerminalData.lean'
if '--check' in sys.argv:assert p.read_text()==s
else:p.write_text(s);(P/'JGn_TERMINAL_INPUTS.json').write_text(json.dumps(data,indent=2)+'\n')
print('terminal generator checked' if '--check' in sys.argv else 'terminal intermediate data generated; diagnostic matches required operand, awaiting kernel certificates')
