"""Focused rejection leaves in the pinned terminal-decoder source cohort."""
from pathlib import Path
root=Path('docs/research/v8-r0-zk-20261009/lean/R1Z');names=[]
common='''import AspisR1TerminalDecoder.Funs
set_option autoImplicit false
namespace R1Z.PV_RJDec_NAME
open Aeneas Aeneas.Std Result AspisR1TerminalDecoder
'''
def emit(name,body):
 (root/('PV_RJDec_'+name+'.lean')).write_text(common.replace('NAME',name)+body+'\n#print axioms rejection\nend R1Z.PV_RJDec_'+name+'\n');names.append('R1Z.PV_RJDec_'+name)
# Each list item is a real ordered guard, with its exact preceding source calls.
configs=[('Snapshot','pool_v1.pair_tree_profile','PoolV1PairLiveSnapshotV1','validate_pool_v1_pair_live_snapshot_v1',[
 ('Pool','core.array.equality.PartialEqArray.eq core.cmp.PartialEqU8 s.pool (Array.repeat 32#usize 0#u8) = ok true','ZeroRequiredBinding',[]),
 ('Domain','core.array.equality.PartialEqArray.eq core.cmp.PartialEqU8 s.deployment_domain (Array.repeat 32#usize 0#u8) = ok true','ZeroRequiredBinding',['hp']),
 ('Sequence','(s.sequence != s.next_pair_index) = true','SequenceIndexMismatch',['hp','hd']),
 ('Capacity','(s.next_pair_index >= capacity) = true','TreeFull',['hp','hd','hs','hc']),
 ('Root','pool_v1.pair_tree_profile.digest_is_canonical s.current_root = ok false','NonCanonicalDigest',['hp','hd','hs','hc','hi'])]),
 ('Payment','pool_v1.payment_relation','CommonPublicV1','validate_common',[
 ('Pool','core.array.equality.PartialEqArray.eq core.cmp.PartialEqU8 s.pool (Array.repeat 32#usize 0#u8) = ok true','ZeroRequiredBinding',[]),
 ('Domain','core.array.equality.PartialEqArray.eq core.cmp.PartialEqU8 s.deployment_domain (Array.repeat 32#usize 0#u8) = ok true','ZeroRequiredBinding',['hp']),
 ('Sequence','(s.anchor_sequence > capacity) = true','InvalidAnchorSequence',['hp','hd','hc']),
 ('Root','pool_v1.payment_relation.digest_is_canonical s.anchor_root = ok false','NonCanonicalDigest',['hp','hd','hc','hi']),
 ('Nullifier','pool_v1.payment_relation.digest_is_canonical s.nullifier = ok false','NonCanonicalDigest',['hp','hd','hc','hi','hr']),
 ('Asset','(s.asset_id >= aspis_core.field.P) = true','NonCanonicalAssetId',['hp','hd','hc','hi','hr','hn'])])]
for group,ns,typ,fn,guards in configs:
 error='PoolV1PairLiveSnapshotErrorV1' if group=='Snapshot' else 'PoolV1PaymentStatementFormatError'
 assumptions={
 'hp':'core.array.equality.PartialEqArray.eq core.cmp.PartialEqU8 s.pool (Array.repeat 32#usize 0#u8) = ok false',
 'hd':'core.array.equality.PartialEqArray.eq core.cmp.PartialEqU8 s.deployment_domain (Array.repeat 32#usize 0#u8) = ok false',
 'hc':f'{ns}.POOL_V1_PAIR_CAPACITY = ok capacity' if group=='Snapshot' else 'pool_v1.incremental_merkle.POOL_V1_LEAF_CAPACITY = ok capacity',
 'hs':'(s.sequence != s.next_pair_index) = false',
 'hi':'(s.next_pair_index >= capacity) = false' if group=='Snapshot' else '(s.anchor_sequence > capacity) = false',
 'hr':f'{ns}.digest_is_canonical '+('s.current_root' if group=='Snapshot' else 's.anchor_root')+' = ok true',
 'hn':f'{ns}.digest_is_canonical s.nullifier = ok true'}
 for leaf,condition,err,pre in guards:
  cap=' (capacity : U64)' if 'capacity' in condition or 'hc' in pre else ''
  b=f'open {ns}\n\ntheorem rejection (s : {typ}){cap}\n'
  for h in pre:b+=f'    ({h} : {assumptions[h]})\n'
  b+=f'    (bad : {condition}) :\n    {fn} s = ok (.Err {error}.{err}) := by\n'
  b+=f'  unfold {fn}\n  simp only ['+', '.join(pre+['bad','bind_tc_ok','Bool.false_eq_true','↓reduceIte'])+']\n'
  emit(group+leaf,b)
(Path('evidence/pv-rjdec-20261028')/'guard-order.json').write_text(__import__('json').dumps(names,indent=2)+'\n')
