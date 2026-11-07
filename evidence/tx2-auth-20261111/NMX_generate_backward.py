from pathlib import Path
import json,re
E=Path(__file__).resolve().parent
ctx={'__file__':str(E/'NMX_generate_steps.py')};exec((E/'NMX_generate_steps.py').read_text().split('manifest=[]')[0],ctx)
types=ctx['types'];plan=json.loads((E/'NMX_FOLD_PLAN.json').read_text());cuts=json.loads((E/'NMX_SEMANTIC_CUTS.json').read_text())
enc={'solana_pubkey.Pubkey':'NMX_Carrier.key','r1_pool_adapter.owned.OwnedAccount':'NMX_Carrier.account','Slice r1_pool_adapter.owned.OwnedAccount':'(fun x => x.val.map NMX_Carrier.account)','U8':'NMX_Carrier.byte','U64':'NMX_Carrier.long','Slice U8':'NMX_Carrier.bytes','Slice (Slice U8)':'(fun x => x.val.map NMX_Carrier.bytes)','Array U8 32#usize':'NMX_Carrier.key','Bool':'id','Box Master':'(fun x => NMX_Carrier.master x.payload)','Box Checkpoint':'(fun x => NMX_Carrier.checkpoint x.payload)','Box Lane':'(fun x => NMX_Carrier.lane x.payload)'}
# independent suffix first; the u64 seed frame is introduced by a separate predecessor.
for lo,hi,mod in [(36,40,'NMX_SemanticF03b'),(31,35,'NMX_SemanticF03a'),(21,30,'NMX_SemanticF02'),(11,20,'NMX_SemanticF01'),(1,10,'NMX_SemanticF00')]:
 imports=['NMX_SF00','NMX_CB00','NMX_DenoteStep','NMX_CommandTransport','NMX_RegistryTransport','NMX_CheckTransport','NMX_SeedFrames','NMX_ScalarBne','NMX_ArrayEqualityCarrier','NMX_IndexTransport']
 nxtmod={40:'NMX_SemanticF04',35:'NMX_SemanticF03b',30:'NMX_SemanticF03a',20:'NMX_SemanticF02',10:'NMX_SemanticF01'}[hi];imports+=[nxtmod]
 if lo==31:imports+=['NMX_U64Carrier']
 s='\n'.join('import '+n for n in imports)+f'''\nset_option autoImplicit false
noncomputable section
namespace {mod}
open Aeneas Aeneas.Std AdapterRw NMX_OwnedPackets NMX_Program NMX_SourceModel NMX_Carrier
attribute [local instance] Classical.propDecidable
'''
 for st in reversed(cuts[lo-1:hi]):
  i=st['occurrence'];g=(i-1)//10;ps=st['params'];kind=st['kind'];var=st['variable'];A=types.get(var,'Unit');encode=enc.get(A,'id');packet=' (lanePacket : NMX_RawChildren.RowSpec_217 ln)'
  if i<=27:packet+='\n (registryPacket : NMX_RawChildren.RowSpec_234 (NMX_DecoderLibrary.install L) D rn)'
  dep=' (count : accounts.val.length = 7)' if i<=7 else ''
  s+=f'''\ntheorem e{i:03d} (owners : Owners) (ln : NMX_RawChildren.LaneNative) (rn : NMX_RawChildren.RegistryNative)
 (L : RSL.PoolLib) (D : RSL.DeployedIds){packet}
 {' '.join(f'({n} : {types[n]})' for n in ps)}{dep} :
 NMX_Heterogeneous.Refines id
  (NMX_Semantics.denote owners ln rn (NMX_SF{g:02d}.p{i:03d} {' '.join(ps)}))
  (NMX_CB{g:02d}.r{i:03d} (NMX_DecoderLibrary.install L) D {' '.join('('+enc[types[n]]+' '+n+')' for n in ps)}) := by
 unfold NMX_SF{g:02d}.p{i:03d} NMX_CB{g:02d}.r{i:03d}
'''
  if kind=='check':
   s+=' rw [NMX_DenoteStep.check]\n'
   if i==21:
    s+=''' have same : (master.payload.initialized_lane_mask != allLanes) =
  (((fun x : Box Master => NMX_Carrier.master x.payload) master).initialized_lane_mask != byte allLanes) :=
  NMX_ScalarBne.byte_ne master.payload.initialized_lane_mask allLanes
 rw [← same]
'''
   s+=' apply NMX_CheckTransport.step\n'
  else:
   if st['syntax_head'].startswith('raw '):s+=' unfold NMX_SourceProgram.raw\n'
   s+=' rw [NMX_DenoteStep.call]\n'
   s+=f' apply NMX_Heterogeneous.bind {encode} id\n'
   arg=None
   if st['syntax_head'].startswith('call '):arg=st['syntax_head'].split(' ',2)[2][:-1]
   if kind in ['key_ne','array_ne']:
    s+=' · change NMX_Heterogeneous.Refines id (NMX_ResultRelation.raw _) (RSL.RS.pure _)\n'
    if kind=='key_ne':s+='   simp only [decide_not,NMX_KeyCarrier.key_equal]\n'
    else:s+='   rw [NMX_ArrayEqualityCarrier.array_ne]\n'
    s+='   exact NMX_HeterogeneousPrimitives.pure id _\n'
   elif kind=='index':
    k=i-1;s+=f' · exact NMX_IndexTransport.inside NMX_Carrier.account accounts {k}#usize (by rw [count]; decide)\n'
   elif kind=='mask':s+=' · exact NMX_HeterogeneousPrimitives.pure byte 255#u8\n'
   elif kind=='data':s+=f' · exact NMX_CommandTransport.data owners ln rn {arg}\n'
   elif kind=='pda':s+=f' · exact NMX_CommandTransport.pda owners ln rn {arg}\n'
   elif kind=='registry':
    s+=''' · change NMX_Heterogeneous.Refines id _
     (NMX_RegistryTransport.model (NMX_DecoderLibrary.install L) D
       ⟨verifier,pool,masterAccount,master.payload,registryAccount,entryAccount,slot⟩)
   exact NMX_RegistryTransport.packet rn (NMX_DecoderLibrary.install L) D registryPacket _
'''
   elif kind in ['master','checkpoint']:s+=f' · exact NMX_BoxCommands.{kind} L owners.{kind} {arg}\n'
   elif kind in ['readonlyAccount','readonlyBuffer','checkpointGuard','distinct']:s+=' · exact NMX_HeterogeneousPrimitives.refl _\n'
   else:
    if kind=='asRef':arg='(Array.to_slice '+arg+')'
    if kind=='key':arg+='.key'
    s+=f' · exact NMX_HeterogeneousPrimitives.pure {encode} {arg}\n'
   s+=f' · intro {var}\n'
  indent=' ' if kind=='check' else '   '
  for line in plan[i-1]['after']:
   assert line.startswith('let ')
   s+='\n'.join(indent+z for z in line.splitlines())+'\n'
  targetmod=nxtmod if i==hi else mod
  call=f'{targetmod}.e{i+1:03d} owners ln rn L D lanePacket'+(' registryPacket' if i+1<=27 else '')+' '+ ' '.join(cuts[i]['params'])+(' count' if i<7 else '')
  if i==23:s+=indent+'simpa only [masterSeeds,bumpSeed,NMX_SeedFrames.master,NMX_SeedFrames.single,NMX_Carrier.master] using ('+call+')\n'
  elif i==35:s+=indent+'simpa only [checkpointSeeds,checkpointMasterSeed,sequenceSeed,checkpointBump,NMX_SeedFrames.checkpoint,NMX_SeedFrames.single,NMX_U64Carrier.value,NMX_Carrier.checkpoint] using ('+call+')\n'
  else:s+=indent+'exact '+call+'\n'
  s+=f'#print axioms e{i:03d}\n'
 s+=f'end {mod}\nend\n';(E/(mod+'.lean')).write_text(s)
