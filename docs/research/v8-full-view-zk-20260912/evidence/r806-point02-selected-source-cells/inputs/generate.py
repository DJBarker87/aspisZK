#!/usr/bin/env python3
import json,hashlib,pathlib,sys,re
R=pathlib.Path('.r21-scratch/r806-point02-selected-cells'); P=R/'PLAN.json'; O=R/'generated'
def sha(p):return hashlib.sha256(pathlib.Path(p).read_bytes()).hexdigest()
def module_for(prefix, n):
 root=pathlib.Path('.r21-scratch/r780-point02-weight-bulk/generated')
 pat=re.compile(rf'^theorem {prefix}_{n:04d}\b', re.M)
 hits=[f for f in root.glob(f'R780Point02WeightChunk*P{0 if prefix == "pw0" else 2}.lean') if pat.search(f.read_text())]
 if len(hits) != 1: raise RuntimeError(f"no unique module for {prefix}_{n:04d}: {hits}")
 return hits[0].stem

def imports_for(es):
 mods=set()
 for e in es:
  prefix='pw0' if e['point']=='p0' else 'pw2'
  for n in [4*e['d']+e['s']+1,4*e['d'],e['s']+1,0]: mods.add(module_for(prefix,n))
 modules=sorted(mods)
 return '\n'.join([
  'import AspisV8R19.R748JointWitnessPointEntry',
  'import AspisV8R19.R743JointSparseEntryBinding',
  'import AspisV8R19.R780Point02WeightPrototype',
  *[f'import AspisV8R19.{m}' for m in modules],
  'open AspisV8R16 AspisV8R17 AspisR19',
  'open AspisV8R19.R740SparsePointObservation AspisV8R19.R743JointSparseEntryBinding',
  'open AspisV8R19.R748JointWitnessPointEntry',
  'open AspisV8R19.R780Point02WeightPrototype',
  *[f'open AspisV8R19.{m}' for m in modules],
  'noncomputable section',
  'set_option autoImplicit false',
  ''
 ])

def render(n,es):
 name=f'R806Point02SelectedChunk{n:02d}'; out=[imports_for(es),f'''namespace AspisV8R19.{name}
abbrev M := ZMod 2147483647
lemma z_eq_zFin10 : z = AspisR19.R750WitnessPointSupport.zFin10 (F := M) := by
  funext i
  fin_cases i <;> rfl
''']
 for e in es:
  p=e['point']; d=e['d'];s=e['s'];v=e['first_limb']; prefix='pw0' if p=='p0' else 'pw2'; pi=0 if p=='p0' else 2
  ns=[4*d+s+1,4*d,s+1,0]
  w=', '.join(f'{prefix}_{x:04d}' for x in ns)
  out.append(f'''/-- Pinned raw matrix row {e['raw_row']}, raw column {e['raw_column']}, flat {e['flat_position']}. -/
theorem {p}_d{d:03d}_s{s}_flat{e['flat_position']:02d} :
    sparseObservation (1073741824:M) (536870912:M) 7 5 (-5) 5 0 7 z {d} {s} (.inr (.inl {pi})) = {v} := by
  rw [z_eq_zFin10]
  unfold sparseObservation
  change ({prefix} {ns[0]} - 7^({s}+1)*{prefix} {ns[1]}) - ({prefix} {ns[2]} - 7^({s}+1)*{prefix} 0) = {v}
  rw [{w}]
  decide
#print axioms {p}_d{d:03d}_s{s}_flat{e['flat_position']:02d}
''')
 out.append(f'end AspisV8R19.{name}\n');return ''.join(out)
def main(check=False):
 plan=json.load(open(P)); es=plan['entries']; files={f'R806Point02SelectedChunk{i:02d}.lean':render(i,es[i*16:(i+1)*16]) for i in range((len(es)+15)//16)}
 man={'plan_sha256':sha(P),'entry_count':len(es),'chunks':[{'file':k,'sha256':hashlib.sha256(v.encode()).hexdigest()} for k,v in files.items()],'scope':'fixed source-shaped p0/p2 sparseObservation entries; literals copied from pinned TSV; no rank/native/privacy claim'}
 files['MANIFEST.json']=json.dumps(man,indent=2)+'\n'
 if check:
  for k,v in files.items():
   if not (O/k).is_file() or (O/k).read_text()!=v:raise SystemExit('mismatch '+k)
  print('check OK',len(es),'entries');return
 O.mkdir(exist_ok=True)
 for k,v in files.items():(O/k).write_text(v)
 print('wrote',len(es),'entries')
if __name__=='__main__':main('--check' in sys.argv)
