"""Reproduce small extraction import/primitive-ABI adaptations; never edit shared sources."""
from pathlib import Path
import hashlib,json,re,sys
R=Path(__file__).resolve().parents[2];E=R/'evidence/pv-alib-20261027';L=R/'docs/research/v8-r0-zk-20261009/lean/R1Z'
check='--check' in sys.argv
for kind in ['Types','Funs']:
 raw=(E/f'circle-owned-{kind}.lean.txt').read_text();s=raw
 assert not re.search(r'\b(axiom|sorry|admit|native_decide|implemented_by)\b',s)
 s=s.replace('import PVALCircleOwned.Types','import R1Z.PV_AL_CircleOwnedTypes')
 if kind=='Funs':
  s=s.replace('import Aeneas\n','import Aeneas\nimport R1Z.PV_AL_ShiftLiterals\n')
  s,n1=re.subn(r'(Std\.U64\.wrapping_shr \w+ )31#i32',r'\g<1>31#u32',s)
  s,n2=re.subn(r'(Std\.U64\.wrapping_shl \w+ )32#i32',r'\g<1>32#u32',s)
  assert (n1,n2)==(2,1),(n1,n2)
  receipt={'normalizations':[{'count':2,'from':'U64 binary >> literal 31 (I32 emission)','to':'wrapping_shr literal 31#u32','generic_word_lemma':'R1Z.PV_AL_ShiftLiterals.shr31'},{'count':1,'from':'U64 binary << literal 32 (I32 emission)','to':'wrapping_shl literal 32#u32','generic_word_lemma':'R1Z.PV_AL_ShiftLiterals.shl32'}],'raw_sha256':hashlib.sha256(raw.encode()).hexdigest(),'extractor_changed':False,'rust_changed':False}
  s='-- Three in-range positive shift-count literals adapted to the current scalar API; see PV_AL_ShiftLiterals.\n'+s
  if not check:(E/'primitive-shift-normalization.json').write_text(json.dumps(receipt,indent=2)+'\n')
 names=re.findall(r'^def ([\w.]+)',s,re.M)
 s+='\n'+''.join('#print axioms PV_AL_CircleOwned.'+n+'\n' for n in names)
 p=L/f'PV_AL_CircleOwned{kind}.lean'
 if check:assert p.read_text()==s,p
 else:p.write_text(s)
print('promotion check passed' if check else 'promoted with exact normalization counts')
