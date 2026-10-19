from pathlib import Path
import hashlib,json,shutil,tarfile,re
base=Path(__file__).resolve().parent
repo=base.parent
out=repo/'docs/research/100bit-spend-path-20261013/evidence/lean-literal-byte-merge-20261015'
(out/'attempts').mkdir(parents=True,exist_ok=True)
(out/'sources').mkdir(exist_ok=True)
for p in base.glob('merge-*.json'):
 shutil.copy2(p,out/'attempts'/p.name)
for p in base.glob('merge-*.log'):
 shutil.copy2(p,out/'attempts'/p.name)
for name in ['LiteralByteProtocol','LiteralByteRunFacts','LiteralOpeningRunGood','SubfieldBatchStage2','ResidualBatch','QueryAccumulator','NaturalEmbedding','QueryResidualBridge','RawPairing']:
 shutil.copy2(base/('R1'+name+'.lean'),out/'sources'/('R1'+name+'.lean'))
for name in ['run-focused.py','lean-with-cache.py','new-cache-pins.json','worker-b-cache-pins.json']:
 if (base/name).exists(): shutil.copy2(base/name,out/name)
for p in base.glob('worker-b-*.json'):
 shutil.copy2(p,out/p.name)
with tarfile.open(out/'target-objects.tar.gz','w:gz') as archive:
 for name in ['LiteralByteProtocol','LiteralByteRunFacts','LiteralOpeningRunGood','SubfieldBatchStage2','ResidualBatch','QueryAccumulator','NaturalEmbedding','QueryResidualBridge','RawPairing']:
  archive.add(base/'objects'/('R1'+name+'.olean'),arcname='objects/R1'+name+'.olean')
axioms=[]
for p in sorted((out/'attempts').glob('*.log')):
 lines=p.read_text().splitlines()
 capture=False
 for line in lines:
  if 'depends on axioms' in line or 'does not depend on any axioms' in line:
   axioms.append(p.name+': '+line); capture=('depends on axioms' in line and ']' not in line)
  elif capture:
   axioms.append(line)
   if ']' in line: capture=False
(out/'axioms.txt').write_text('\n'.join(axioms)+'\n')
print(out)
