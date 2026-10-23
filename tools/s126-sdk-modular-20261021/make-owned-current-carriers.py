#!/usr/bin/env python3
"""Field/constructor-preserving maps; reject mismatched error carrier shapes."""
from pathlib import Path
import re,json,hashlib
R=Path(__file__).resolve().parents[2];B=R/'docs/research/100bit-spend-path-20261013';O=B/'lean-candidates/s126-caller-boundary-20261021'
old=(B/'lean/extracted-terminal-decoder-20261016/AspisR1TerminalDecoder/Types.lean').read_text();fresh=(O/'S2OwnedStage1TypesV1.lean').read_text()
s='''import S2OwnedStage1ReachabilityV1
import CurrentCompactFirstCompositionV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisS2OwnedStage1.CurrentCarrier
'''
pairs=[('Afterstate','pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1','next_pair_index next_root next_frontier'),('Snapshot','pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotV1','pool deployment_domain sequence next_pair_index current_root frontier'),('Transfer','pool_v1.payment_relation.PoolV1PrivateTransferPublicV1','pool deployment_domain anchor_sequence anchor_root nullifier asset_id recipient_commitment change_commitment'),('Withdrawal','pool_v1.payment_relation.PoolV1WithdrawalPublicV1','pool deployment_domain anchor_sequence anchor_root nullifier asset_id amount destination_token_account change_commitment')]
F='AspisS2OwnedStage1.aspis_statement.';D='AspisR1TerminalDecoder.';C='AspisR1CurrentCaller.aspis_statement.'
for pref,src,dst in [('fromDecoder',D,F),('toDecoder',F,D),('toCurrent',F,C),('fromCurrent',C,F)]:
 for name,path,fields in pairs:
  s+='\ndef '+pref+name+' (x : '+src+path+') : '+dst+path+' :=\n  {'+', '.join(f+':=x.'+f for f in fields.split())+'}\n'
 path='pool_v1.pair_tree_profile.PoolV1PairLatePublicStatementV1'
 s+='\ndef '+pref+'Transition (x : '+src+path+') : '+dst+path+' :=\n  {live_snapshot:='+pref+'Snapshot x.live_snapshot,candidate_afterstate:='+pref+'Afterstate x.candidate_afterstate}\n'
 if pref in ['fromDecoder','toDecoder']:
  path='pool_v1.pair_forest_terminal.PoolV1PairForestTerminalCommonV1'
  fs='master_account checkpoint_account selected_lane_account output_lane checkpoint_sequence historical_global_anchor'.split()
  s+='\ndef '+pref+'Common (x : '+src+path+') : '+dst+path+' :=\n  {'+', '.join(f+':=x.'+f for f in fs)+',lane_transition:='+pref+'Transition x.lane_transition}\n'
  path='pool_v1.pair_forest_terminal.PoolV1PairForestTerminalStatementV1'
  s+='\ndef '+pref+'Statement : '+src+path+' → '+dst+path+'\n  | .PrivateTransfer c p => .PrivateTransfer ('+pref+'Common c) ('+pref+'Transfer p)\n  | .Withdrawal c p => .Withdrawal ('+pref+'Common c) ('+pref+'Withdrawal p)\n'
 else:
  path='pool_v1.pair_forest_semantic_terminal.r0.Public'
  s+='\ndef '+pref+'Public : '+src+path+' → '+dst+path+'\n  | .Transfer p t => .Transfer ('+pref+'Transfer p) ('+pref+'Transition t)\n  | .Withdrawal p t => .Withdrawal ('+pref+'Withdrawal p) ('+pref+'Transition t)\n'
errors=[('TreeError','pool_v1.incremental_merkle.PoolV1TreeError'),('AccountError','pool_v1.pair_forest_accounts.PoolV1PairForestAccountErrorV1'),('PaymentError','pool_v1.payment_relation.PoolV1PaymentStatementFormatError'),('SnapshotError','pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotErrorV1'),('AfterstateError','pool_v1.pair_terminal.PoolV1PairVerifierTransportErrorV1'),('TransitionError','pool_v1.pair_tree_profile.PoolV1PairLatePublicStatementErrorV1'),('DecodeError','pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1')]
def constructors(text,name):
 m=re.search(r'^inductive '+re.escape(name)+r'\s+where\n',text,re.M);assert m,name
 tail=text[m.end():];end=re.search(r'\n(?:/--|@\[|def |instance |structure |inductive )',tail);tail=tail[:end.start()] if end else tail
 rows=[]
 for row in re.finditer(r'^\| (\w+) :([\s\S]*?)(?=^\||\Z)',tail,re.M):
  ts=[' '.join(x.split()) for x in row[2].split('→')];assert ts[-1]==name,(name,ts)
  rows.append((row[1],ts[:-1]))
 return rows
errmap=dict((path,name) for name,path in errors);audit=[]
for name,path in errors:
 a=constructors(old,path);b=constructors(fresh,'aspis_statement.'+path)
 assert a==[(c,[x.removeprefix('aspis_statement.') for x in ts]) for c,ts in b],(name,a,b)
 audit.append(dict(path=path,constructors=a))
 for pref,src,dst in [('fromDecoder',D,F),('toDecoder',F,D)]:
  s+='\ndef '+pref+name+' : '+src+path+' → '+dst+path+'\n'
  for c,ts in a:
   args=['x'+str(i) for i in range(len(ts))]
   s+='  | .'+c+(' '+' '.join(args) if args else '')+' => .'+c
   for x,t in zip(args,ts):assert t in errmap,t;s+=' ('+pref+errmap[t]+' '+x+')'
   s+='\n'
 # Inverse through nested constructors is a structural proof, not enumeration
 # of arbitrary field values or replacement by a single error code.
 for pref,inv,src in [('fromDecoder','toDecoder',D),('toDecoder','fromDecoder',F)]:
  s+='\ntheorem '+pref+name+'_roundtrip (x : '+src+path+') : '+inv+name+' ('+pref+name+' x)=x := by\n  cases x <;> simp only ['+pref+name+', '+inv+name
  for earlier,_ in errors[:errors.index((name,path))]:s+=', '+pref+earlier+'_roundtrip'
  s+=']\n'
s+='''
theorem decoder_statement_roundtrip (s : AspisR1TerminalDecoder.PublicBinding.Statement) :
    toDecoderStatement (fromDecoderStatement s)=s := by cases s <;> rfl
theorem fresh_statement_roundtrip (s : Reachability.Statement) :
    fromDecoderStatement (toDecoderStatement s)=s := by cases s <;> rfl
theorem current_public_roundtrip (p : AspisR1CurrentCaller.FirstComposition.Public) :
    toCurrentPublic (fromCurrentPublic p)=p := by cases p <;> rfl
theorem fresh_public_roundtrip (p : Reachability.Public) :
    fromCurrentPublic (toCurrentPublic p)=p := by cases p <;> rfl
theorem selected_public (s : AspisR1TerminalDecoder.PublicBinding.Statement) :
    (do
      let p ← aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalStatementV1.semantic_public (fromDecoderStatement s)
      ok (toCurrentPublic p)) =
    ok (AspisR1CurrentCaller.FirstComposition.toCurrentPublic
      (AspisR1PublicPreparation.PreparationBinding.preparationPublic s)) := by
  cases s <;> rfl

#print axioms decoder_statement_roundtrip
#print axioms fresh_statement_roundtrip
#print axioms current_public_roundtrip
#print axioms selected_public
#print axioms fromDecoderDecodeError_roundtrip
end AspisS2OwnedStage1.CurrentCarrier
'''
(O/'S2OwnedCurrentCarrierV1.lean').write_text(s)
(O/'owned-decoder-carrier-audit.json').write_text(json.dumps(dict(schema='focused-extractor-proof-packet-v1',retained_types_sha256=hashlib.sha256(old.encode()).hexdigest(),fresh_types_sha256=hashlib.sha256(fresh.encode()).hexdigest(),error_shapes=audit,qualification='Every decoder error constructor and nested payload preserved. Full statement/common/public fields copied in both directions; checked roundtrips and selector transport. No error quotient or simplified statement carrier.'),indent=2)+'\n')
