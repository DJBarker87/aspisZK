from pathlib import Path
import json,re,sys
R=Path(__file__).resolve().parents[2];P=Path(__file__).resolve().parent
p=2147483647
add=lambda a,b:tuple((x+y)%p for x,y in zip(a,b))
def cm(a,b):return ((a[0]*b[0]-a[1]*b[1])%p,(a[0]*b[1]+a[1]*b[0])%p)
def qm(a,b):return add(cm(a[:2],b[:2]),cm(cm(a[2:],b[2:]),(2,1)))+add(cm(a[:2],b[2:]),cm(a[2:],b[:2]))
def mul(a,b):return add(qm(a[:4],b[:4]),qm(qm(a[4:],b[4:]),(0,0,1,0)))+add(qm(a[:4],b[4:]),qm(a[4:],b[:4]))
def q(a):return '⟨⟨'+','.join(map(str,a[:2]))+'⟩,⟨'+','.join(map(str,a[2:]))+'⟩⟩'
def lit(a):return '⟨'+q(a[:4])+','+q(a[4:])+'⟩'
s=(R/'lean/JFq_Kappa.lean').read_text();base=tuple(map(int,re.findall(r'(\d+)#u32',s.split('def decoded :')[1].split('\ntheorem decode')[0])));assert len(base)==8
rows=[base];prev=base
for n in range(2,7):
 val=mul(prev,base);rows.append(val);name=f'JHl_Kappa{n:02}'
 s='import JFq_Kappa\n'+(f'import JHl_Kappa{n-1:02}\n' if n>2 else '')+f'''set_option autoImplicit false
noncomputable section
namespace AspisR1.{name}
abbrev FE := AspisWideTower.WideExact
def value : FE := {lit(val)}
/-- One bounded exact field multiplication for the remaining prepared claim. -/
theorem step : '''+('CheckpointBytes5Output.ofE JFq_Kappa.scalar' if n==2 else f'JHl_Kappa{n-1:02}.value')+f'''*CheckpointBytes5Output.ofE JFq_Kappa.scalar=value := by
  change ({lit(prev)} : FE)*{lit(base)}={lit(val)}
  ext <;> norm_num [AspisWideTower.wideU,AspisV8R15.ExactTowerBase.qm31R,
    AspisV8R15.ExactTowerBase.M31Exact,AspisV8R15.ExactTowerBase.P] <;> decide
#print axioms step
theorem source : CheckpointBytes5Output.ofE JFq_Kappa.scalar^{n}=value := by
'''+('  rw [pow_two]\n  exact step\n' if n==2 else f'  rw [pow_succ,JHl_Kappa{n-1:02}.source,step]\n')+f'''#print axioms source
end AspisR1.{name}
end
'''
 if '--check' in sys.argv:assert (R/'lean'/f'{name}.lean').read_text()==s,name
 else:(R/'lean'/f'{name}.lean').write_text(s)
 prev=val
(P/'JHl_KAPPA_PREFLIGHT.json').write_text(json.dumps(rows,indent=2)+'\n')
print('5 one-multiplication kappa certificates validated')
