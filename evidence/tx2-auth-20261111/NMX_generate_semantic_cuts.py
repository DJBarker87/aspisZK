"""Dictionary-free source syntax and canonical reference continuations.
Definitions only: every occurrence and the reference factor need separate proof.
"""
from pathlib import Path
import json,re
E=Path(__file__).resolve().parent
ctx={'__file__':str(E/'NMX_generate_steps.py')};exec((E/'NMX_generate_steps.py').read_text().split('manifest=[]')[0],ctx)
types=ctx['types'];plan=json.loads((E/'NMX_FOLD_PLAN.json').read_text())
canon={
'Ops':'UNUSED','solana_pubkey.Pubkey':'RSL.B32','Slice r1_pool_adapter.owned.OwnedAccount':'List RSL.OwnedAccount',
'r1_pool_adapter.owned.OwnedAccount':'RSL.OwnedAccount','U8':'UInt8','U64':'UInt64','Slice U8':'RSL.Bytes',
'Slice (Slice U8)':'List RSL.Bytes','Array U8 32#usize':'RSL.B32','Bool':'Bool','Box Master':'RSL.Master',
'Box Checkpoint':'RSL.Checkpoint','Box Lane':'RSL.LaneState','Box Snapshot':'RSL.LiveSnapshot'}
def selected(s):
 s=s.replace('raw ops.op16','raw (.ok 255#u8)')
 return re.sub(r'core\.cmp\.PartialEq\.ne\.trait_default\s*\(solana_pubkey\.Pubkey\.Insts\.CoreCmpPartialEqPubkey ops\) (\w+) (\w+)',lambda m:'(.ok (!(decide ('+m[1]+' = '+m[2]+'))))',s)
def ctext(s):return s.replace('master.payload','master').replace('checkpoint.payload','checkpoint').replace('lane.payload','lane').replace('live.payload','live')
purelets={
'bumpSeed':'[master.bump]','masterSeeds':'[RSL.SEED_MASTER,mintSeed,bumpSeed]',
'checkpointMasterSeed':'masterKey.bytes','sequenceSeed':'RSL.u64le checkpoint.checkpoint_sequence',
'checkpointBump':'[checkpoint.bump]','checkpointSeeds':'[RSL.SEED_CHECKPOINT,checkpointMasterSeed,sequenceSeed,checkpointBump]',
'laneIdSeed':'[outputLane]','laneBump':'[lane.bump]','laneSeeds':'[RSL.SEED_LANE,laneMasterSeed,laneIdSeed,laneBump]'}
metadata=[]
for group in range(6):
 lo=10*group+1;hi=min((group+1)*10,55)
 si=['NMX_Skeleton']+([f'NMX_SF{group+1:02d}'] if hi<55 else [])
 ci=['NMX_CanonicalTarget']+([f'NMX_CB{group+1:02d}'] if hi<55 else [])
 sf='\n'.join('import '+x for x in si)+f'''\nset_option autoImplicit false
noncomputable section
namespace NMX_SF{group:02d}
open Aeneas Aeneas.Std AdapterRw NMX_OwnedPackets NMX_Program NMX_SourceProgram
attribute [local instance] Classical.propDecidable
'''
 cb='\n'.join('import '+x for x in ci)+f'''\nset_option autoImplicit false
namespace NMX_CB{group:02d}
open RSL
'''
 for st in reversed(plan[lo-1:hi]):
  i=st['n'];ps=[n for n in st['params'] if n!='ops'];sparams=' '.join(f'({n} : {types[n]})' for n in ps);cparams=' '.join(f'({n} : {canon[types[n]]})' for n in ps)
  term=selected(st['term']);var=st['var'];after=st['after']
  if i==55:
   payload=after[0].removeprefix('pure ');sp='.ret '+payload;cp='RSL.RS.pure '+ctext(payload)
  else:
   nxt=plan[i];nargs=' '.join(n for n in nxt['params'] if n!='ops');ns=(i)//10
   sp=f'NMX_SF{ns:02d}.p{i+1:03d} {nargs}';cp=f'NMX_CB{ns:02d}.r{i+1:03d} L D {nargs}'
   for block in reversed(after):
    m=re.match(r'let (\w+) := ',block);assert m,(i,block)
    sp=block+'\n'+sp
    cp='let '+m[1]+' := '+purelets[m[1]]+'\n'+cp
  sf+=f'\ndef p{i:03d} {sparams} : Program Auth :=\n NMX_Program.bind (NMX_SourceProgram.{term}) (fun {var} =>\n'+ '\n'.join('  '+x for x in sp.splitlines())+')\n'
  kind='';expr=''
  if term.startswith('raw '):
   if term.startswith('raw (Slice.index_usize'):
    k=re.search(r' (\d)#usize',term)[1];expr=f'RSL.RS.index accounts {k}';kind='index'
   elif 'PartialEqArray.ne' in term:
    # The only array comparisons in233 are32-byte keys/bindings.
    _,rest=term.split('core.cmp.PartialEqU8',1);rest=ctext(rest).strip().removesuffix(')')
    x,y=rest.split();expr=f'RSL.RS.pure (decide ({x} ≠ {y}))';kind='array_ne'
   elif '255#u8' in term:expr='RSL.RS.pure RSL.ALL_LANES_MASK';kind='mask'
   else:
    m=re.search(r'decide \((\w+) = (\w+)\)',term);assert m,term
    expr=f'RSL.RS.pure (decide ({m[1]} ≠ {m[2]}))';kind='key_ne'
  elif term.startswith('check '):
   expr='RSL.RS.check ('+ctext(term[6:])+') .invalidAccountData';kind='check'
  else:
   m=re.fullmatch(r'call \(\.(\w+) (.*)\)',term,re.S);assert m,term
   cmd,args=m.groups();args=ctext(args);kind=cmd
   if cmd=='readonlyBuffer':expr=f'RSL.RS.ofExcept (RSL.readonlyBuffer {args})'
   elif cmd=='checkpointGuard':expr=f'RSL.RS.ofExcept (RSL.verifierCheckpoint {args})'
   elif cmd=='readonlyAccount':expr=f'RSL.RS.ofExcept (RSL.readonlyAccount {args})'
   elif cmd=='distinct':expr='RSL.RS.ofExcept (RSL.requireDistinct [proof,masterAccount,checkpointAccount,laneAccount,registryAccount,entryAccount,verifierCheckpoint])'
   elif cmd=='data':expr=f'RSL.RS.ofExcept (RSL.OwnedAccount.data {args})'
   elif cmd=='key':expr=f'RSL.RS.pure {args}.key'
   elif cmd in ['toBytes','fromBytes']:expr=f'RSL.RS.pure ({args})'
   elif cmd=='asRef':expr=f'RSL.RS.pure {args}.bytes'
   elif cmd=='master':expr=f'RSL.decodeMasterBox L {args}'
   elif cmd=='checkpoint':expr=f'RSL.decodeCheckpointBox L {args}'
   elif cmd=='lane':expr=f'RSL.Spec.call RSL.TX2_217.Domain RSL.TX2_217.Ref {args}'
   elif cmd=='pda':expr=f'RSL.pdaOrErr {args}'
   elif cmd=='registry':expr='RSL.Spec.call RSL.TX2_234.Domain (RSL.TX2_234.Ref L D) ⟨verifier,pool,masterAccount,master,registryAccount,entryAccount,slot⟩'
   elif cmd=='snapshot':expr=f'RSL.RS.bind (RSL.RS.lift RSL.Spec.alloc) (fun _ => RSL.RS.pure ({args} : RSL.LiveSnapshot))'
   else:raise RuntimeError(cmd)
  cb+=f'\ndef r{i:03d} (L : RSL.PoolLib) (D : RSL.DeployedIds) {cparams} : RSL.RS RSL.Authenticated :=\n RSL.RS.bind ({expr}) (fun {var} =>\n'+ '\n'.join('  '+x for x in cp.splitlines())+')\n'
  metadata.append(dict(occurrence=i,params=ps,kind=kind,model_head=expr,syntax_head=term,variable=var))
 sf+=f'end NMX_SF{group:02d}\nend\n';cb+=f'end NMX_CB{group:02d}\n'
 (E/f'NMX_SF{group:02d}.lean').write_text(sf);(E/f'NMX_CB{group:02d}.lean').write_text(cb)
(E/'NMX_SEMANTIC_CUTS.json').write_text(json.dumps(sorted(metadata,key=lambda x:x['occurrence']),indent=1)+'\n')
