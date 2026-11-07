from pathlib import Path
import json,re
E=Path(__file__).resolve().parent
ctx={'__file__':str(E/'NMX_generate_steps.py')};exec((E/'NMX_generate_steps.py').read_text().split('manifest=[]')[0],ctx)
types=ctx['types'];plan=json.loads((E/'NMX_FOLD_PLAN.json').read_text());cuts=json.loads((E/'NMX_SEMANTIC_CUTS.json').read_text())
enc={'solana_pubkey.Pubkey':'NMX_Carrier.key','r1_pool_adapter.owned.OwnedAccount':'NMX_Carrier.account','U8':'NMX_Carrier.byte','U64':'NMX_Carrier.long','Slice U8':'NMX_Carrier.bytes','Slice (Slice U8)':'(fun x => x.val.map NMX_Carrier.bytes)','Array U8 32#usize':'NMX_Carrier.key','Bool':'id','Box Master':'(fun x => NMX_Carrier.master x.payload)','Box Checkpoint':'(fun x => NMX_Carrier.checkpoint x.payload)','Box Lane':'(fun x => NMX_Carrier.lane x.payload)'}
head='''import NMX_SF04
import NMX_CB04
import NMX_TailIndependent
import NMX_DenoteStep
import NMX_CommandTransport
import NMX_CheckTransport
import NMX_SeedFrames
import NMX_ScalarBne
import NMX_ArrayEqualityCarrier
set_option autoImplicit false
noncomputable section
namespace NMX_SemanticF04
open Aeneas Aeneas.Std AdapterRw NMX_OwnedPackets NMX_Program NMX_SourceModel NMX_Carrier
attribute [local instance] Classical.propDecidable
'''
s=head
for st in reversed(cuts[40:50]):
 i=st['occurrence'];ps=st['params'];var=st['variable'];kind=st['kind'];A=types.get(var,'Unit');encode=enc.get(A,'id');packet=' (lanePacket : NMX_RawChildren.RowSpec_217 ln)' if i==41 else ''
 s+=f'''\ntheorem e{i:03d} (owners : Owners) (ln : NMX_RawChildren.LaneNative) (rn : NMX_RawChildren.RegistryNative)
 (L : RSL.PoolLib) (D : RSL.DeployedIds){packet}
 {' '.join(f'({n} : {types[n]})' for n in ps)} :
 NMX_Heterogeneous.Refines id
  (NMX_Semantics.denote owners ln rn (NMX_SF04.p{i:03d} {' '.join(ps)}))
  (NMX_CB04.r{i:03d} (NMX_DecoderLibrary.install L) D {' '.join('('+enc[types[n]]+' '+n+')' for n in ps)}) := by
 unfold NMX_SF04.p{i:03d} NMX_CB04.r{i:03d}
'''
 if kind=='check':
  s+=' rw [NMX_DenoteStep.check]\n'
  if i==45:s+=' rw [← NMX_ScalarBne.byte_ne]\n'
  s+=' apply NMX_CheckTransport.step\n'
 else:
  if st['syntax_head'].startswith('raw '):s+=' unfold NMX_SourceProgram.raw\n'
  s+=' rw [NMX_DenoteStep.call]\n'
  s+=f' apply NMX_Heterogeneous.bind {encode} id\n'
  if kind=='key_ne':
   s+=' · change NMX_Heterogeneous.Refines id (NMX_ResultRelation.raw _) (RSL.RS.pure _)\n   simp only [decide_not,NMX_KeyCarrier.key_equal]\n   exact NMX_HeterogeneousPrimitives.pure id _\n'
  elif kind=='array_ne':s+=' · change NMX_Heterogeneous.Refines id (NMX_ResultRelation.raw _) (RSL.RS.pure _)\n   rw [NMX_ArrayEqualityCarrier.array_ne]\n   exact NMX_HeterogeneousPrimitives.pure id _\n'
  elif kind=='pda':s+=' · exact NMX_CommandTransport.pda owners ln rn laneSeeds pool\n'
  elif kind=='lane':s+=' · exact NMX_CommandTransport.lane owners ln rn lanePacket laneBytes\n'
  else:
   arg=re.search(r'\.\w+ (\w+)\)',st['syntax_head'])[1]
   if kind=='asRef':arg='(Array.to_slice '+arg+')'
   if kind=='key':arg+='.key'
   s+=f' · exact NMX_HeterogeneousPrimitives.pure {encode} {arg}\n'
  s+=f' · intro {var}\n'
 indent=' ' if kind=='check' else '   '
 for line in plan[i-1]['after']:
  assert line.startswith('let ')
  s+='\n'.join(indent+z for z in line.splitlines())+'\n'
 nxt=cuts[i];mod='NMX_TailIndependent' if i==50 else 'NMX_SemanticF04'
 call=f'{mod}.e{i+1:03d} owners ln rn L D '+ ' '.join(nxt['params'])
 if i==46:s+=indent+'simpa only [NMX_SeedFrames.lane,NMX_SeedFrames.single] using ('+call+')\n'
 else:s+=indent+'exact '+call+'\n'
 s+=f'#print axioms e{i:03d}\n'
s+='end NMX_SemanticF04\nend\n';(E/'NMX_SemanticF04.lean').write_text(s)
