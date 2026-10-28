from pathlib import Path
import re,json,sys
R=Path(__file__).resolve().parents[2];P=Path(__file__).resolve().parent
p=2147483647
add=lambda a,b:tuple((x+y)%p for x,y in zip(a,b))
def cm(a,b):return ((a[0]*b[0]-a[1]*b[1])%p,(a[0]*b[1]+a[1]*b[0])%p)
def qm(a,b):return add(cm(a[:2],b[:2]),cm(cm(a[2:],b[2:]),(2,1)))+add(cm(a[:2],b[2:]),cm(a[2:],b[:2]))
def mul(a,b):return add(qm(a[:4],b[:4]),qm(qm(a[4:],b[4:]),(0,0,1,0)))+add(qm(a[:4],b[4:]),qm(a[4:],b[:4]))
def q(a):return '⟨⟨'+','.join(map(str,a[:2]))+'⟩,⟨'+','.join(map(str,a[2:]))+'⟩⟩'
def lit(a):return '⟨'+q(a[:4])+','+q(a[4:])+'⟩'
def nums(s,typ='u8'):return tuple(map(int,re.findall(r'(\d+)#'+typ,s)))
def field(name):return nums((R/'lean'/f'{name}.lean').read_text().split('def decoded :')[1].split('\ntheorem decode')[0],'u32')
def words(bs):return tuple(int.from_bytes(bytes(bs[i:i+4]),'little') for i in range(0,len(bs),4))
source=(R/'lean/JFu_Q25InputBase.lean').read_text()
rows=[[] for _ in range(6)]
for j in range(116):
 bs=nums(re.search(r'def p'+str(j).zfill(2)+r' : List U8 := (.*)',source)[1]);assert len(bs)==32
 rows[j//29].append(words(bs))
wire=[]
for i in range(15):
 s=(R/'lean'/f'JFx_DataProof{i:02}.lean').read_text()
 for match in re.finditer(r'def c\d+ : List U8 := (.*)',s):
  v=match[1];wire.extend([0]*int(re.search(r'replicate (\d+)',v)[1]) if 'replicate' in v else nums(v))
assert len(wire)==57607
for j in range(29):
 rows[4].append(words(wire[6567+16*j:6567+16*(j+1)])+(0,)*4)
 rows[5].append(words(nums((R/'lean'/f'JGi_Y1Cell{j:02}.lean').read_text().split('def arr :')[1].split('\ntheorem selected')[0])))
gamma=field('JFq_Gamma');kappa=field('JFq_Kappa');claim=field('JFq_Claim');zero=(0,)*8
hs=[]
for row in rows:
 h=[zero]*30
 for j in reversed(range(29)):h[j]=add(row[j],mul(gamma,h[j+1]))
 hs.append(h)
w=(1,)+(0,)*7;total=zero
for row in hs:
 w=mul(w,kappa);total=add(total,mul(w,row[0]))
assert total==claim,(total,claim)
D=dict(gamma=gamma,kappa=kappa,claim=claim,rows=rows,horner=hs,numeric_match=True)
(P/'JHm_PREFLIGHT.json').write_text(json.dumps(D,indent=2)+'\n')
files={}
name='JHm_Arithmetic'
s='import JFq_Gamma\nset_option autoImplicit false\nnoncomputable section\nnamespace AspisR1.JHm_Arithmetic\nabbrev FE := AspisWideTower.WideExact\n'
s+='def gamma : FE := '+lit(gamma)+'\n'
s+='theorem gamma_value : CheckpointBytes5Output.ofE JFq_Gamma.scalar=gamma := rfl\n#print axioms gamma_value\n'
s+='def row (p : Nat) : List FE := match p with\n'
for i,row in enumerate(rows):s+=f'  | {i} => ['+','.join(lit(a) for a in row)+']\n'
s+='  | _ => []\ndef horner (g : FE) : List FE → FE\n  | [] => 0\n  | x::xs => x+g*horner g xs\n'
s+='end AspisR1.JHm_Arithmetic\nend\n';files[name]=s
for i in range(6):
 for b in range(8):
  start= max(0,29-4*(b+1));end=29-4*b
  if end<=0:continue
  name=f'JHm_Dot{i}_{b}'
  s='import JHm_Arithmetic\n'+(f'import JHm_Dot{i}_{b-1}\n' if b else '')
  s+=f'set_option autoImplicit false\nnoncomputable section\nnamespace AspisR1.{name}\nopen JHm_Arithmetic\n'
  for j in reversed(range(start,end)):
   s+=f'def h{j:02} : FE := {lit(hs[i][j])}\n'
   prior='0' if j==28 else (f'h{j+1:02}' if j+1<end else f'JHm_Dot{i}_{b-1}.h{j+1:02}')
   s+=f'theorem step{j:02} : ({lit(rows[i][j])} : FE)+gamma*{prior}=h{j:02} := by\n'
   s+=f'  change ({lit(rows[i][j])} : FE)+{lit(gamma)}*{lit(hs[i][j+1])}={lit(hs[i][j])}\n'
   s+='  ext <;> norm_num [AspisWideTower.wideU,AspisV8R15.ExactTowerBase.qm31R,\n    AspisV8R15.ExactTowerBase.M31Exact,AspisV8R15.ExactTowerBase.P] <;> decide\n'
   s+=f'#print axioms step{j:02}\n'
  s+=f'theorem source : horner gamma ((JHm_Arithmetic.row {i}).drop {start})=h{start:02} := by\n'
  # Avoid large recursive normalization: unfold precisely four constructor steps.
  if b==0:s+='  change '+('(' *0)+f'horner gamma ['+','.join(lit(a) for a in rows[i][start:])+f']=h{start:02}\n'
  else:
   s+=f'  have tail := JHm_Dot{i}_{b-1}.source\n'
   s+=f'  change horner gamma ['+','.join(lit(a) for a in rows[i][end:])+f']=JHm_Dot{i}_{b-1}.h{end:02} at tail\n'
   s+=f'  change horner gamma ['+','.join(lit(a) for a in rows[i][start:])+f']=h{start:02}\n'
  s+='  rw ['+','.join(['horner']*(end-start)+( ['horner'] if b==0 else ['tail'])+[f'step{j:02}' for j in reversed(range(start,end))])+']\n'
  s+=f'#print axioms source\nend AspisR1.{name}\nend\n';files[name]=s
for name,s in files.items():
 if '--check' in sys.argv:assert (R/'lean'/f'{name}.lean').read_text()==s,name
 else:(R/'lean'/f'{name}.lean').write_text(s)
print('Verified six 29-term Horner computations and kappa-weighted claim match; generated',len(files),'modules')
