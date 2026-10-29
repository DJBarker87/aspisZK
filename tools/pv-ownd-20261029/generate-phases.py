from pathlib import Path
R=Path(__file__).resolve().parents[2];L=R/'docs/research/v8-r0-zk-20261009/lean/R1Z'
for phase,count,src in [('Private',21,'privateLinks'),('Append',20,'appendLinks')]:
 names=[f'PV_OWND_{phase}{n:02d}' for n in range(count)];name=f'PV_OWND_{phase}Phase'
 text=''.join(f'import R1Z.{n}\n' for n in names)
 text+=f'''set_option autoImplicit false
namespace R1Z.{name}
open PV_OWND_LegacySource PV_OWN_Link
def values : List Link := '''+' ++ '.join(n+'.values' for n in names)+f'''
theorem source : {src}=values := by
 unfold {src}
 have range : List.range {count}=['''+','.join(map(str,range(count)))+'''] := rfl
 rw [range]
 simp only [List.flatMap_cons,List.flatMap_nil,List.append_nil,'''+','.join(n+'.source' for n in names)+''']
 rfl

theorem count : values.length='''+str(count*(3 if phase=='Private' else 2))+''' := by
 simp only [values,List.length_append,'''+','.join(n+'.count' for n in names)+''']
#print axioms source
#print axioms count
attribute [local irreducible] values
end R1Z.'''+name+'\n'
 (L/(name+'.lean')).write_text(text)
