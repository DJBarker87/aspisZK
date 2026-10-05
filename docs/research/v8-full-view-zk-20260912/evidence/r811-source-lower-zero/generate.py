from pathlib import Path
import re,ast,json,hashlib
R=Path('.').resolve(); DOC=R/'docs/research/v8-full-view-zk-20260912/lean/AspisV8R19'
active_text=(DOC/'R801LiteralActiveEntries.lean').read_text()
line=next(x for x in active_text.splitlines() if x.startswith('def activeCodes'))
codes=ast.literal_eval(line.split(':=',1)[1].strip())
assert len(codes)==214
inv=json.loads((R/'.r21-scratch/r724-block-order-maps/evidence/inputs/index_inventory.json').read_text())['original_row_to_flat_position_inverse']
assert len(inv)==222 and len(set(inv))==222
# theorem and support map from saved literal row files
code_chunk={}; support={}
for p in DOC.glob('R804LiteralSourceRowsChunk*.lean'):
 s=p.read_text()
 for m in re.finditer(r'def literalRow(\d+) \(j : Fin 222\) : M := ([^\n]+)',s):
  code=int(m.group(1)); body=m.group(2)
  code_chunk[code]=p.stem
  support[code]=[int(x) for x in re.findall(r'j\.val = (\d+)',body)]
# special row114
s=(DOC/'R804LiteralSourceRow114.lean').read_text()
m=re.search(r'def literalRow114 \(j : Fin 222\) : M :=(.*?)\ntheorem literalSourceMatrix_row114',s,re.S)
code_chunk[114]='R804LiteralSourceRow114'; support[114]=[int(x) for x in re.findall(r'j\.val = (\d+)',m.group(1))]
s=(DOC/'R804LiteralSourceRow1022.lean').read_text()
m=re.search(r'def literalRow1022 \(j : Fin 222\) : M := ([^\n]+)',s)
code_chunk[1022]='R804LiteralSourceRow1022'; support[1022]=[int(x) for x in re.findall(r'j\.val = (\d+)',m.group(1))]
assert all(c in code_chunk for c in codes),[c for c in codes if c not in code_chunk]
rows=[]
for original in range(214):
 flat=inv[original]
 if flat==35: continue
 rows.append({'original':original,'flat':flat,'code':codes[original],'chunk':code_chunk[codes[original]],'support':support[codes[original]],'block':None})
assert len(rows)==213
# data-only proof chunk generator; compile group in <=4 rows
import argparse
pa=argparse.ArgumentParser();pa.add_argument('--chunk',type=int,required=True);pa.add_argument('--start',type=int,required=True);pa.add_argument('--count',type=int,required=True);pa.add_argument('--check',action='store_true');a=pa.parse_args()
assert 1<=a.count<=4
sel=rows[a.start:a.start+a.count];assert len(sel)==a.count
num=f'{a.chunk:02}'
mod=f'R811SourceLowerZeroChunk{num}'
imports=['AspisV8R19.R807SourceBlock01Binding']+[f'AspisV8R19.{x}' for x in sorted({x['chunk'] for x in sel if x['chunk'] not in ('R804LiteralSourceRow114','R804LiteralSourceRow1022')})]
if any(x['chunk']=='R804LiteralSourceRow114' for x in sel): imports.append('AspisV8R19.R804LiteralSourceRow114')
if any(x['chunk']=='R804LiteralSourceRow1022' for x in sel): imports.append('AspisV8R19.R804LiteralSourceRow1022')
text='\n'.join('import '+x for x in imports)+'''\n\nset_option autoImplicit false\nset_option maxRecDepth 32768\nnamespace AspisV8R19.'''+mod+'''\nopen AspisV8R19.R807SourceBlock01Binding\nopen AspisV8R19.R806LiteralBlockLayout\nopen AspisV8R19.R724BlockOrderMaps\nopen AspisV8R19.R804LiteralSourceRow114\nopen AspisV8R19.R799LiteralSourceMatrix\nopen AspisV8R19.R801LiteralActiveEntries\nopen AspisV8R19.R748JointWitnessPointEntry\n'''
for c in sorted({x['chunk'] for x in sel}):text+=f'open AspisV8R19.{c}\n'
text+='''\nnoncomputable section\nlocal instance : Nontrivial R807SourceBlock01Binding.M := ⟨⟨0,1,by decide⟩⟩\n'''
def and_proj(i,n): return ('.2'*i if i==n-1 and n>1 else '.' + '.'.join(['2']*i+['1']))
for x in sel:
 flat=x['flat']; orig=x['original']; code=x['code']; sup=x['support']
 fsup=' ∧ '.join(f'(colOrder j).val ≠ {n}' for n in sup) or 'True'
 simp=', '.join(f'if_neg (excluded j h){and_proj(i,len(sup))}' if len(sup)>1 else 'if_neg (excluded j h)' for i in range(len(sup)))
 target=f'(⟨{flat},by decide⟩ : Fin 222)'
 active=f'(⟨{orig},by decide⟩ : Fin 214)'
 text+=f'''\ntheorem rowFlat{flat}_lower_zero (j : Fin 222)\n    (h : blockLabel j < blockLabel {target}) :\n    reorderedSourceMatrix {target} j = 0 := by\n  change (literalSourceMatrix halfSelected quarterSelected alphaSelected uSelected vSelected\n    kappaSelected tauSelected z) (activePosition {active}) (colOrder j) = 0\n  rw [literalSourceMatrix_row{code}]\n  have excluded : ∀ j : Fin 222, blockLabel j < blockLabel {target} →\n      {fsup} := by decide\n  simp only [literalRow{code}, {simp}]\n\n#print axioms rowFlat{flat}_lower_zero\n'''
text+='end\nend AspisV8R19.'+mod+'\n'
out=R/'.r21-scratch/r811-source-lower-zero'/f'{mod}.lean'
if a.check:
 old=out.read_text();assert old==text,(out,'differs')
else:
 out.write_text(text)
manifest={'schema':'r811-source-lower-zero-chunk-v1','module':mod,'start':a.start,'count':a.count,'rows':sel,'imports':imports,'generator_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),'source_sha256':hashlib.sha256(text.encode()).hexdigest(),'pinned_inputs':{str(DOC/'R801LiteralActiveEntries.lean'):hashlib.sha256((DOC/'R801LiteralActiveEntries.lean').read_bytes()).hexdigest(),str(DOC/'R724BlockOrderMaps.lean'):hashlib.sha256((DOC/'R724BlockOrderMaps.lean').read_bytes()).hexdigest(),str(DOC/'R804LiteralSourceRow114.lean'):hashlib.sha256((DOC/'R804LiteralSourceRow114.lean').read_bytes()).hexdigest()}}
mp=R/'.r21-scratch/r811-source-lower-zero'/f'{mod}.manifest.json';mp.write_text(json.dumps(manifest,indent=2)+'\n')
print(json.dumps({'source':str(out),'sha256':manifest['source_sha256'],'rows':sel,'imports':imports},indent=2))
