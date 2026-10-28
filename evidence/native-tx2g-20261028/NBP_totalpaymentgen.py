from pathlib import Path
for kind in ['Transfer','Withdrawal']:
 name='NBP_'+kind+'Decode';lower=kind.lower();fun='decode_pool_v1_'+('private_transfer' if kind=='Transfer' else 'withdrawal')+'_public_v1';p=Path('lean/'+name+'.lean');s=p.read_text();a=s.index('#print axioms fixed')
 full=f'''/-- All slice lengths, including rejection before any fixed-width read. -/
theorem result (bytes : Slice U8) :
    pool_v1.payment_relation.{fun} bytes =
      if h : bytes.val.length=216 then ok ({lower}_decoded (⟨bytes.val,h⟩ : Array U8 216#usize))
      else ok (.Err .WrongLength) := by
  by_cases h : bytes.val.length=216
  · rw [dif_pos h]
    change pool_v1.payment_relation.{fun} (⟨bytes.val,h⟩ : Array U8 216#usize).to_slice = _
    exact fixed _
  · rw [dif_neg h]
    simp [pool_v1.payment_relation.{fun},core.array.TryFromSharedArraySlice.try_from,
      Slice.len,Slice.length,h,core.result.Result.map_err,
      pool_v1.payment_relation.{fun}.closure.Insts.CoreOpsFunctionFnOnceTupleTryFromSliceErrorPoolV1PaymentStatementFormatError,
      pool_v1.payment_relation.{fun}.closure.Insts.CoreOpsFunctionFnOnceTupleTryFromSliceErrorPoolV1PaymentStatementFormatError.call_once,
      core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
      core.convert.FromSame]
#print axioms result
'''
 p.write_text(s[:a]+full+s[a:])
