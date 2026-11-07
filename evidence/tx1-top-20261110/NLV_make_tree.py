from pathlib import Path
E=Path(__file__).resolve().parent;G=E/'NLV_generated'
pre='''import NLV_Algebra
set_option autoImplicit false
noncomputable section
namespace AspisR1.NLV_Tree
open Aeneas Aeneas.Std Result AspisR1CurrentCaller NLJ_Tx1
open CheckpointBytes5Effect (Code)
local instance : MonadLift Result Code where monadLift := CheckpointBytes5Effect.liftResult
'''
names=['guard','parse','scan','markParsed','zero','prepare','accumulator','markPrepare','foldedSlice','foldedCopy','foldedUnwrap','batch0','markMerkle','geometry','pending','query','finishPending','checkpoint','markCheckpoint','returned']
params={'prepare':'(g : Scratch)','accumulator':'(g : Scratch) (p : verifier.Prepared)','markPrepare':'(g : Scratch) (p : verifier.Prepared) (a : verifier.Accumulator)','foldedSlice':'(g : Scratch) (p : verifier.Prepared) (a : verifier.Accumulator)','foldedCopy':'(g : Scratch) (p : verifier.Prepared) (a : verifier.Accumulator) (slice : Slice U8)','foldedUnwrap':'(g : Scratch) (p : verifier.Prepared) (a : verifier.Accumulator) (r : core.result.Result Root core.array.TryFromSliceError)','batch0':'(g : Scratch) (p : verifier.Prepared) (a : verifier.Accumulator) (root : Root)','markMerkle':'(g : Scratch) (p : verifier.Prepared) (a : verifier.Accumulator)','geometry':'(g : Scratch) (p : verifier.Prepared) (a : verifier.Accumulator)','pending':'(g : Scratch) (p : verifier.Prepared) (a : verifier.Accumulator) (geom : verifier.QueryGeometry)','query':'(g : Scratch) (p : verifier.Prepared) (a : verifier.Accumulator) (geom : verifier.QueryGeometry) (pending : verifier.BatchedWeights)','finishPending':'(p : verifier.Prepared) (a : verifier.Accumulator) (pending : verifier.BatchedWeights)','checkpoint':'(p : verifier.Prepared) (a : verifier.Accumulator)','markCheckpoint':'(bytes : alloc.vec.Vec U8)','returned':'(bytes : alloc.vec.Vec U8)'}
import re
s=Path('evidence/tx1-prepare-20261110/NLJ_generated/NLJ_Tx1Step.lean').read_text();s=s[s.index(' match s.locals with\n')+len(' match s.locals with\n'):s.index('end AspisR1.NLJ_Tx1')]
branches=re.split(r'^ \| ',s,flags=re.M)[1:];data={}
for b in branches:
 lhs,body=b.split(' =>\n',1) if ' =>\n' in b else b.split(' => ',1)
 site=lhs.split()[0][1:];args=' '.join(lhs.split()[1:]);data[site]=(args,body)
for site in reversed(names):
 args,body=data[site]
 # Translate only the administrative continuation. Child code remains byte-identical.
 body=re.sub(r'pure \(\.inl (.*?)\)\n',r'pure \1\n',body)
 def plain(m):
  target=m[1];return 'suffix_'+target+' cfg i'
 body=re.sub(r'pure \(\.inr \(advance s \.(\w+)\)\)',plain,body)
 body=re.sub(r'pure \(\.inr \(advance s \(\.(\w+) (.*)\)\)\)',lambda m:'suffix_'+m[1]+' cfg i '+m[2],body)
 # nextOrError tails have one bound result variable.
 body=re.sub(r'pure \(nextOrError s r \(fun (\w+) => \.(\w+)(?: (.*))?\)\)',lambda m:'match r with\n   | .Err e => pure (.Err e)\n   | .Ok '+m[1]+' => suffix_'+m[2]+' cfg i'+(' '+m[3] if m[3] else ''),body)
 body=body.replace(' o.',' (ops cfg).').replace(' o\n',' (ops cfg)\n').replace(' o\r',' (ops cfg)\r').replace('WideExact.ZERO o','WideExact.ZERO (ops cfg)').replace('OFF_FOLDED_ROOT o','OFF_FOLDED_ROOT (ops cfg)').replace('OFF_ROUND1 o','OFF_ROUND1 (ops cfg)')
 # unparenthesized final returned body
 body=body.replace('pure (.inl (.Ok bytes))','pure (.Ok bytes)')
 if not body.startswith(' '):body='   '+body
 assert 'advance s' not in body and 'nextOrError' not in body,(site,body)
 pre+='\ndef suffix_'+site+' (cfg : Configuration) (i : Input) '+params.get(site,'')+' : Code Out := do\n'+body
pre+='\ndef denote (cfg : Configuration) (s : NLJ_Tx1.State) : Code Out :=\n match s.locals with\n'
for site in names:
 args,_=data[site];pre+=' | .'+site+(' '+args if args else '')+' => suffix_'+site+' cfg s.input'+(' '+args if args else '')+'\n'
pre+='end AspisR1.NLV_Tree\nend\n';(G/'NLV_Tree.lean').write_text(pre)
(E/'NLV_SITES.json').write_text(__import__('json').dumps({s:dict(args=data[s][0],params=params.get(s,''),rank=20-i) for i,s in enumerate(names)},indent=2))
