from pathlib import Path
B=Path(__file__).resolve().parents[2]/'docs/research/100bit-spend-path-20261013/lean-candidates/s126-caller-boundary-20261021'
header='''import CurrentCompactTx1ReachabilityV1
import S6DecoderScopedReuseV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1CurrentCaller.FirstComposition
open AspisR1CurrentCaller
namespace Old := AspisR1PublicPreparation
abbrev OldPublic := Old.pool_v1.pair_forest_semantic_terminal.r0.Public
abbrev Public := aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public
'''.replace('namespace Old := AspisR1PublicPreparation','')
# Lean namespace aliases use local notation for full prefixes only via open? Fully qualify names instead.
header=header.replace('Old.','AspisR1PublicPreparation.')
code=header
pairs=[('Afterstate','pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1','next_pair_index next_root next_frontier'),('Snapshot','pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotV1','pool deployment_domain sequence next_pair_index current_root frontier'),('Transfer','pool_v1.payment_relation.PoolV1PrivateTransferPublicV1','pool deployment_domain anchor_sequence anchor_root nullifier asset_id recipient_commitment change_commitment'),('Withdrawal','pool_v1.payment_relation.PoolV1WithdrawalPublicV1','pool deployment_domain anchor_sequence anchor_root nullifier asset_id amount destination_token_account change_commitment')]
for prefix,old,new in [('toCurrent','AspisR1PublicPreparation.','aspis_statement.'),('toRetained','aspis_statement.','AspisR1PublicPreparation.')]:
 for name,path,fields in pairs:
  code+='\ndef '+prefix+name+' (x : '+old+path+') : '+new+path+' :=\n  {'+', '.join(f+':=x.'+f for f in fields.split())+'}\n'
 path='pool_v1.pair_tree_profile.PoolV1PairLatePublicStatementV1'
 code+='\ndef '+prefix+'Transition (x : '+old+path+') : '+new+path+' :=\n  {live_snapshot:='+prefix+'Snapshot x.live_snapshot,candidate_afterstate:='+prefix+'Afterstate x.candidate_afterstate}\n'
 code+='\ndef '+prefix+'Public : '+('OldPublic → Public' if prefix=='toCurrent' else 'Public → OldPublic')+'\n  | .Transfer p t => .Transfer ('+prefix+'Transfer p) ('+prefix+'Transition t)\n  | .Withdrawal p t => .Withdrawal ('+prefix+'Withdrawal p) ('+prefix+'Transition t)\n'
code+='''
/-- Every original public field is retained, for both variants. -/
theorem current_retained_roundtrip (p : Public) : toCurrentPublic (toRetainedPublic p)=p := by
  cases p <;> rfl

theorem retained_current_roundtrip (p : OldPublic) : toRetainedPublic (toCurrentPublic p)=p := by
  cases p <;> rfl

def retainedPhase : verifier.Phase → AspisR1PublicPreparation.FirstCaller.Phase
'''
for name,args in [('Parsed',''),('Semantic',''),('SemanticPart','i'),('Prepare',''),('CheckpointRead',''),('Merkle','i'),('Query','i'),('QueryPart','i j'),('CheckpointWrite',''),('Relation',''),('Final','')]:
 code+='  | .'+name+(' '+args if args else '')+' => .'+name+(' '+args if args else '')+'\n'
code+='''
/-- The actual current compact tx1 on the field-preserving public carrier.
The observer map preserves callbacks, not merely acceptance. Release callers
supply None, so the actual source verifier receives None. -/
def currentTx1 (ops : Ops) (D : aspis_core.digest.Digest32 Unit)
    (pub : OldPublic) (bytes proof : Slice U8) (k : Usize) (digest : Unit)
    (obs : Option (AspisR1PublicPreparation.FirstCaller.Phase → Result Unit)) :
    Result (core.result.Result (alloc.vec.Vec U8) verifier.Error) :=
  verifier.candidate.tx1 ops D (toCurrentPublic pub) bytes proof k digest
    (obs.map fun callback => fun phase => callback (retainedPhase phase))

/-- Complete retained first/first_decoded source control, with its tx1 child
now instantiated by the current compact caller, rather than a free callback. -/
def firstCurrent {E : Type} (invalidAccountData : E) (ops : Ops)
    (D : aspis_core.digest.Digest32 Unit) (error : verifier.Error → Result E)
    (bytes proof : Slice U8) (k : Usize) :=
  AspisR1PublicPreparation.RepinS6First.first invalidAccountData
    (currentTx1 ops D) error bytes proof k

/-- One enclosing first success derives its checked decoder, same public and
exact original byte/proof/k arguments, then the same-run compact preparation,
semantic verification, Prepared::new and post-scratch continuation. The old
independent decoder-success, selected-public, child-tx1, selected-View,
semantic-result, preparation-success and scratch witnesses are not premises. -/
theorem first_current_prepared_new {E : Type} (invalidAccountData : E)
    (ops : Ops) (D : aspis_core.digest.Digest32 Unit) (error : verifier.Error → Result E)
    (bytes proof : Slice U8) (k : Usize) (out : alloc.vec.Vec U8)
    (h : firstCurrent invalidAccountData ops D error bytes proof k=ok (.Ok out)) :
    ∃ (s : AspisR1PublicPreparation.FirstCaller.DecoderStatement),
      AspisR1PublicPreparation.S6DecoderScopedReuseV1.decodeActual bytes=ok (.Ok s) ∧
      k=compact.SPLIT ∧ ∃ (zero : aspis_core.field.wide_exact.WideExact)
        (prepared : verifier.Prepared) (scratch : Array aspis_core.field.wide_exact.WideExact 29#usize)
        (semantic y1 : Slice U8) (v : verifier.View) (sem : r1_semantic.Verified Unit),
        ops.op5 proof semantic y1=ok (.Ok v) ∧
        ops.op9 D (toCurrentPublic (AspisR1PublicPreparation.PreparationBinding.preparationPublic s))
          v.semantic () none=ok (.Ok sem) ∧
        ops.op8 D sem v () (Array.repeat 29#usize zero)=ok (.Ok prepared,scratch) ∧
        Tx1Reachability.afterPrepare ops D bytes proof k () none prepared scratch=ok (.Ok out) := by
  obtain ⟨s,pub,hd,hpub,htx⟩ := AspisR1PublicPreparation.RepinS6First.first_success
    invalidAccountData (currentTx1 ops D) error bytes proof k out h
  subst pub
  change verifier.candidate.tx1 ops D
    (toCurrentPublic (AspisR1PublicPreparation.PreparationBinding.preparationPublic s))
    bytes proof k () none=ok (.Ok out) at htx
  obtain ⟨hk,zero,prepared,scratch,semantic,y1,v,sem,hview,hsem,hnew,htail⟩ :=
    Tx1Reachability.tx1_prepared_new ops D
      (toCurrentPublic (AspisR1PublicPreparation.PreparationBinding.preparationPublic s))
      bytes proof k () out htx
  exact ⟨s,hd,hk,zero,prepared,scratch,semantic,y1,v,sem,hview,hsem,hnew,htail⟩

#print axioms current_retained_roundtrip
#print axioms retained_current_roundtrip
#print axioms currentTx1
#print axioms first_current_prepared_new
end AspisR1CurrentCaller.FirstComposition
'''
(B/'CurrentCompactFirstCompositionV1.lean').write_text(code)
