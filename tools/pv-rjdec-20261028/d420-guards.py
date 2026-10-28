"""Emit small source-prefix laws; no native Runtime observation is selected."""
from pathlib import Path
import sys
def emit(p,s):
 if "--check" in sys.argv: assert p.read_text()==s,p
 else: p.write_text(s)
D=Path(__file__).resolve().parents[2]/'docs/research/v8-r0-zk-20261009/lean/R1Z'
base='set_option autoImplicit false\nnoncomputable section\nnamespace R1Z.PV_RJDec_NAME\nopen Aeneas Aeneas.Std Result AspisR1TerminalDecoder PV_W_TypedEffects\nvariable [ProverRwFull.ExternalTypes] [ProverRwFull.ExternalFuns]\n'
# Snapshot length is a pure guard, with no dictionary call before rejection.
s='import R1Z.PV_RJDec_ParserR12\n'+base.replace('NAME','SnapshotGuard')
s+='''theorem wrong_length (bytes : Slice U8)
    (wrong : (Slice.len bytes != pool_v1.pair_tree_profile.POOL_V1_PAIR_LIVE_SNAPSHOT_BYTES) = true) :
    erase (inferInstance : ProverRwFull.ExternalFuns) (PV_RJDec_ParserR12.program bytes) =
      .ok (.Err pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotErrorV1.WrongLength) := by
  simp only [PV_RJDec_ParserR12.program,wrong,Bool.true_eq,↓reduceIte,erase_pure]
#print axioms wrong_length
end R1Z.PV_RJDec_SnapshotGuard
'''
emit(D/'PV_RJDec_SnapshotGuard.lean',s)
for name,mod,space,fn,const,err in [('TerminalGuard','ParserR20','pair_forest_terminal','decode_pool_v1_pair_forest_terminal_statement_v1','POOL_V1_PAIR_FOREST_TERMINAL_STATEMENT_BYTES','PoolV1PairForestTerminalFormatErrorV1'),('AfterGuard','ParserR15','pair_terminal','decode_pool_v1_pair_verified_afterstate_v1','POOL_V1_PAIR_VERIFIED_AFTERSTATE_BYTES','PoolV1PairVerifierTransportErrorV1')]:
 q='pool_v1.'+space+'.';call=q+const;decode=q+fn
 s='import R1Z.PV_RJDec_'+mod+'\n'+base.replace('NAME',name)
 for kind,ctor,bind in [('failure','.fail error','bind_tc_fail'),('divergence','.div','bind_tc_div')]:
  args=' (error : Aeneas.Std.Error)' if kind=='failure' else ''
  s+='theorem '+kind+' (bytes : Slice U8)'+args+'\n    (first : '+call+' = '+ctor+') :\n    erase (inferInstance : ProverRwFull.ExternalFuns) (PV_RJDec_'+mod+'.program bytes) = '+ctor+' := by\n  rw [PV_RJDec_'+mod+'.source]\n  simp only ['+decode+',first,'+bind+']\n#print axioms '+kind+'\n'
 s+='''theorem wrong_length (bytes : Slice U8) (expected : Usize)
    (first : CALL = .ok expected)
    (wrong : (Slice.len bytes != expected) = true) :
    erase (inferInstance : ProverRwFull.ExternalFuns) (PV_RJDec_MOD.program bytes) =
      .ok (.Err ERR.WrongLength) := by
  rw [PV_RJDec_MOD.source]
  simp only [DECODE,first,bind_tc_ok,wrong,Bool.true_eq,↓reduceIte]
#print axioms wrong_length
'''.replace('CALL',call).replace('MOD',mod).replace('ERR',q+err).replace('DECODE',decode)
 if mod=='ParserR15': s=s.replace('PV_RJDec_ParserR15.source]','PV_RJDec_ParserR15.source_chunk]').replace(decode,'PV_RJDec_ParserR15.reference')
 s+='end R1Z.PV_RJDec_'+name+'\n';emit(D/('PV_RJDec_'+name+'.lean'),s)
s='import R1Z.PV_RJDec_ParserR17\nimport R1Z.PV_RJDec_ParserR10\n'+base.replace('NAME','PaymentPrefix')
for name,mod,fn in [('transfer','ParserR17','decode_pool_v1_private_transfer_public_v1'),('withdrawal','ParserR10','decode_pool_v1_withdrawal_public_v1')]:
 for kind,ctor,bind in [('failure','.fail error','bind_tc_fail'),('divergence','.div','bind_tc_div')]:
  args=' (error : Aeneas.Std.Error)' if kind=='failure' else ''
  s+='theorem '+name+'_'+kind+' (bytes : Slice U8)'+args+'\n    (first : core.array.TryFromSharedArraySlice.try_from 216#usize bytes = '+ctor+') :\n    erase (inferInstance : ProverRwFull.ExternalFuns) (PV_RJDec_'+mod+'.program bytes) = '+ctor+' := by\n  rw [PV_RJDec_'+mod+'.source]\n  simp only [pool_v1.payment_relation.'+fn+',first,'+bind+']\n#print axioms '+name+'_'+kind+'\n'
s+='end R1Z.PV_RJDec_PaymentPrefix\n';emit(D/'PV_RJDec_PaymentPrefix.lean',s)
