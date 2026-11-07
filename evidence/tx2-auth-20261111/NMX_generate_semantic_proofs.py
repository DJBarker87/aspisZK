from pathlib import Path
import json,re
E=Path(__file__).resolve().parent
ctx={'__file__':str(E/'NMX_generate_steps.py')};exec((E/'NMX_generate_steps.py').read_text().split('manifest=[]')[0],ctx)
types=ctx['types'];plan=json.loads((E/'NMX_FOLD_PLAN.json').read_text());cuts=json.loads((E/'NMX_SEMANTIC_CUTS.json').read_text())
enc={'solana_pubkey.Pubkey':'key','Slice r1_pool_adapter.owned.OwnedAccount':'(fun x => x.val.map account)','r1_pool_adapter.owned.OwnedAccount':'account','U8':'byte','U64':'long','Slice U8':'bytes','Slice (Slice U8)':'(fun x => x.val.map bytes)','Array U8 32#usize':'key','Bool':'id','Box Master':'(fun x => master x.payload)','Box Checkpoint':'(fun x => checkpoint x.payload)','Box Lane':'(fun x => lane x.payload)','Box Snapshot':'(fun x => snapshot x.payload)'}
def at(n):return '('+enc[types[n]]+' '+n+')'
for g in reversed(range(6)):
 lo=g*10+1;hi=min(lo+9,55)
 imports=[f'NMX_SF{g:02d}',f'NMX_CB{g:02d}','NMX_DenoteStep','NMX_BoxCommands','NMX_CommandTransport','NMX_IndexTransport','NMX_ScalarBne','NMX_ArrayEqualityCarrier']
 if hi<55:imports+=[f'NMX_SemanticF{g+1:02d}']
 s='\n'.join('import '+n for n in imports)+f'''\nset_option autoImplicit false
noncomputable section
namespace NMX_SemanticF{g:02d}
open Aeneas Aeneas.Std AdapterRw NMX_OwnedPackets NMX_Program NMX_SourceModel NMX_Carrier
attribute [local instance] Classical.propDecidable
'''
 for st in reversed(cuts[lo-1:hi]):
  i=st['occurrence'];ps=st['params'];kind=st['kind'];var=st['variable'];psdecl=' '.join(f'({n} : {types[n]})' for n in ps)
  deps=''
  if i<=7:deps=' (count : accounts.val.length = 7)'
  s+=f'''\ntheorem e{i:03d} (owners : Owners) (ln : NMX_RawChildren.LaneNative) (rn : NMX_RawChildren.RegistryNative)
 (L : RSL.PoolLib) (D : RSL.DeployedIds)
 (lanePacket : NMX_RawChildren.RowSpec_217 ln)
 (registryPacket : NMX_RawChildren.RowSpec_234 (NMX_DecoderLibrary.install L) D rn)
 {psdecl}{deps} :
 NMX_Heterogeneous.Refines id
  (NMX_Semantics.denote owners ln rn (NMX_SF{g:02d}.p{i:03d} {' '.join(ps)}))
  (NMX_CB{g:02d}.r{i:03d} (NMX_DecoderLibrary.install L) D {' '.join(at(n) for n in ps)}) := by
 unfold NMX_SF{g:02d}.p{i:03d} NMX_CB{g:02d}.r{i:03d}
'''
  if kind=='check':
   s+=' rw [NMX_DenoteStep.check]\n'
   s+=' fail "Unimplemented carrier step"\n' # intentionally generator WIP, never submit until replaced
   continue
  s+=' rw [NMX_DenoteStep.call]\n' if not st['syntax_head'].startswith('raw ') else ''
  A=types.get(var,'Unit');encode=enc.get(A,'id');
  if A=='Unit':encode='id'
  s+=f' apply NMX_Heterogeneous.bind {encode} id\n'
  if kind in ['toBytes','fromBytes','asRef','key','mask']:
   raw=st['syntax_head'];v=re.search(r'\.\w+ (\w+)\)',raw)
   arg=v[1] if v else '255#u8'
   if kind=='key':arg+=' .key' # overwritten below
   if kind=='key':arg=v[1]+'.key'
   if kind=='asRef':arg='(Array.to_slice '+v[1]+')'
   s+=f' · exact NMX_HeterogeneousPrimitives.pure {encode} {arg}\n'
  elif kind=='snapshot':
   payload=st['syntax_head'].split('.snapshot ',1)[1][:-1]
   s+=f' · exact NMX_HeterogeneousPrimitives.allocation {encode} (⟨owners.snapshot,{payload}⟩ : Box Snapshot)\n'
  elif kind in ['master','checkpoint']:
   arg=st['syntax_head'].split()[-1][:-1]
   s+=f' · exact NMX_BoxCommands.{kind} L owners.{kind} {arg}\n'
  else:s+=' · fail "Unimplemented carrier step"\n'
  s+=f' · intro {var}\n'
  if i==55:s+='   exact NMX_HeterogeneousPrimitives.pure id _\n'
  else:
   nxt=cuts[i];ng=i//10;args=' '.join(nxt['params'])
   s+=f'   exact NMX_SemanticF{ng:02d}.e{i+1:03d} owners ln rn L D lanePacket registryPacket {args}'+(' count' if i<7 else '')+'\n'
  s+=f'#print axioms e{i:03d}\n'
 s+=f'end NMX_SemanticF{g:02d}\nend\n'
 (E/f'NMX_SemanticF{g:02d}.lean').write_text(s)
