from pathlib import Path
import json,re,hashlib
P=Path(__file__).resolve().parent;R=P.parents[1]
shapes=json.loads((P/'JGu_LEVEL_SHAPES.json').read_text())
roots=json.loads((R/'evidence/joint-fixture24-20261027/JGr_MERKLE_PREFLIGHT.json').read_text())['trees']
physical=[0,0,0];parents=[0,0,0]
for shape in shapes:
 t=shape['tree'];h=shape['height'];ns=shape['module'];text=(R/f'lean/{ns}.lean').read_text()
 assert shape['cursor_start']==32*physical[t]
 assert 'theorem source' in text and '#print axioms source' in text
 for row in shape['rows']:
  n=int(row['n']);assert f'JGu_ParentCalls{t}.source{n:03}' in text
  assert roots[t]['hashes'][n]['kind']=='parent'
  assert roots[t]['hashes'][n]['level']==h
  parents[t]+=1
  if not row['pair']:
   assert row['before']==physical[t];physical[t]+=1
   if ns!='JGu_Level0_00':assert f'theorem read{row["w"]:02}' in text
 assert shape['cursor_end']==32*physical[t]
 if h==17:assert physical[t]==roots[t]['consumed']
assert physical==[138,138,120];assert parents==[147,147,129]
for f in (R/'lean').glob('JGu_*.lean'):
 s=f.read_text()
 assert not re.search(r'\b(sorry|admit|native_decide|axiom)\b',s),f
 assert not re.search(r'set_option\s+(maxRecDepth|maxHeartbeats)',s),f
 assert 'unfold JFp_SHADigest.digest' not in s,f
result=dict(classification='source-shape/manifest validation, not a prover replay',levels=len(shapes),physical_reads=physical,native_parent_calls=parents,capacities=[146,146,128],padding_bytes=[256,256,256],sha_generated=False,sha_reduced=False)
(P/'JGu_MANIFEST_CHECK.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result))
