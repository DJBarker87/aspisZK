from pathlib import Path
import re,json,hashlib
src=Path('/tmp/terminal-v4-model-sources-20261019/AspisR1SelectedMaskProbe/Types.lean')
raw=src.read_text();changes=[]
pat=r'@\[discriminant isize\]\n(inductive ([\w.]+)[\s\S]*?)(?=\n/--|\nend AspisR1SelectedMaskProbe)'
def adapt(m):
 body,name=m.group(1),m.group(2)
 ctors=re.findall(r'^\| (\w+)\s*:\s*([\s\S]*?)(?=^\||\Z)',body,re.M)
 assert ctors,name
 cases=[(c,t.count('→')) for c,t in ctors]
 aux='\n-- Naming-only expansion of the generated discriminant attribute.\n'
 aux+=f'def {name}.read_discriminant (x : {name}) : Isize :=\n  match x with\n'
 aux+=''.join(f'  | .{c}'+(' _'*n)+f' => {i}#isize\n' for i,(c,n) in enumerate(cases))
 aux+=f'\ninstance _root_.AspisR1SelectedMaskProbe.{name}.instDiscriminant :\n    Aeneas.Std.Discriminant {name} Isize where\n  read_discriminant := {name}.read_discriminant\n'
 replacement=body+aux;changes.append((m.group(0),replacement,{'type':name,'constructors':cases}))
 return replacement
new=re.sub(pat,adapt,raw);assert len(changes)==5
inverse=new
for before,after,_ in reversed(changes):assert inverse.count(after)==1;inverse=inverse.replace(after,before)
assert inverse==raw
out=Path('/tmp/root-terminal-named-types-20261019');out.mkdir(exist_ok=True)
(out/'Types-named.lean').write_text(new)
sha=lambda b:hashlib.sha256(b).hexdigest()
(out/'adapter-pins.json').write_text(json.dumps({'raw_source':str(src),'raw_sha256':sha(raw.encode()),'adapted_sha256':sha(new.encode()),'inverse_recovers_raw':True,'changes':[c[2] for c in changes],'scope':'Only five generated discriminant attributes expanded to same constructor reader with qualified instance names. No Rust/source function change. Current terminal dependent objects still require coherent replay.'},indent=2)+'\n')
print(json.dumps({'changes':len(changes),'adapted_sha256':sha(new.encode())}))
