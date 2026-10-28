from pathlib import Path
import json,re,sys
R=Path(__file__).resolve().parents[2];P=Path(__file__).resolve().parent
D=json.loads((P/'JHm_PREFLIGHT.json').read_text())
# Reuse generator arithmetic definitions without running its output path.
ns={};exec((P/'JHm_generate.py').read_text().split('source=(R/')[0].replace('R=Path(__file__).resolve().parents[2];P=Path(__file__).resolve().parent',''),dict(__file__=str(P/'JHm_generate.py')),ns)
# Explicit finite tower arithmetic for a preflight only.
p=2147483647
add=lambda a,b:tuple((x+y)%p for x,y in zip(a,b))
def cm(a,b):return ((a[0]*b[0]-a[1]*b[1])%p,(a[0]*b[1]+a[1]*b[0])%p)
def qm(a,b):return add(cm(a[:2],b[:2]),cm(cm(a[2:],b[2:]),(2,1)))+add(cm(a[:2],b[2:]),cm(a[2:],b[:2]))
def mul(a,b):return add(qm(a[:4],b[:4]),qm(qm(a[4:],b[4:]),(0,0,1,0)))+add(qm(a[:4],b[4:]),qm(a[4:],b[:4]))
def q(a):return '⟨⟨'+','.join(map(str,a[:2]))+'⟩,⟨'+','.join(map(str,a[2:]))+'⟩⟩'
def lit(a):return '⟨'+q(a[:4])+','+q(a[4:])+'⟩'
files={};name='JHm_Dots'
s=''.join(f'import JHm_Dot{i}_7\n' for i in range(6))+'import JHl_ClaimKappa\nset_option autoImplicit false\nnoncomputable section\nnamespace AspisR1.JHm_Dots\nopen JHm_Arithmetic\n'
s+='def value (p : Nat) : FE := match p with\n'+''.join(f'  | {i} => JHm_Dot{i}_7.h00\n' for i in range(6))+'  | _ => 0\n'
s+='theorem source (p : Fin 6) : horner gamma (JHm_Arithmetic.row p.val)=value p.val := by\n  fin_cases p\n'
for i in range(6):s+=f'  · exact JHm_Dot{i}_7.source\n'
s+='#print axioms source\ndef term (i : Nat) : FE := JHl_ClaimKappa.value (i+1)*value i\nend AspisR1.JHm_Dots\nend\n';files[name]=s
w=(1,)+(0,)*7;total=(0,)*8
for i in range(6):
 w=mul(w,D['kappa']);v=D['horner'][i][0];t=mul(w,v);new=add(total,t);name=f'JHm_Weighted{i}'
 s='import JHm_Dots\n'+(f'import JHm_Weighted{i-1}\n' if i else '')+'import JFq_Claim\n'
 s+=f'set_option autoImplicit false\nnoncomputable section\nnamespace AspisR1.{name}\nopen JHm_Arithmetic\ndef value : FE := {lit(new)}\ndef product : FE := {lit(t)}\n'
 s+=f'theorem term : JHm_Dots.term {i}=product := by\n  change ({lit(w)} : FE)*{lit(v)}={lit(t)}\n'
 s+='  ext <;> norm_num [AspisWideTower.wideU,AspisV8R15.ExactTowerBase.qm31R,\n    AspisV8R15.ExactTowerBase.M31Exact,AspisV8R15.ExactTowerBase.P] <;> decide\n#print axioms term\n'
 s+=f'theorem add : '+('0' if i==0 else f'JHm_Weighted{i-1}.value')+f'+product=value := by\n  change ({lit(total)} : FE)+{lit(t)}={lit(new)}\n'
 s+='  ext <;> norm_num [AspisWideTower.wideU,AspisV8R15.ExactTowerBase.qm31R,\n    AspisV8R15.ExactTowerBase.M31Exact,AspisV8R15.ExactTowerBase.P] <;> decide\n#print axioms add\n'
 s+=f'theorem source : ∑ j∈Finset.range {i+1},JHm_Dots.term j=value := by\n'
 if i==0:s+='  rw [Finset.sum_range_succ,Finset.sum_range_zero,term,add]\n'
 else:s+=f'  rw [Finset.sum_range_succ,JHm_Weighted{i-1}.source,term,add]\n'
 s+='#print axioms source\n'
 if i==5:s+='theorem retained : value=CheckpointBytes5Output.ofE JFq_Claim.scalar := rfl\n#print axioms retained\n'
 s+=f'end AspisR1.{name}\nend\n';files[name]=s;total=new
assert tuple(D['claim'])==total
for name,s in files.items():
 if '--check' in sys.argv:assert (R/'lean'/f'{name}.lean').read_text()==s,name
 else:(R/'lean'/f'{name}.lean').write_text(s)
print('Validated6 weighted products and partial sums in7 modules')
