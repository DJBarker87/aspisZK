from pathlib import Path
p=Path('docs/research/100bit-spend-path-20261013/lean/ExtractedTerminalWithdrawalSuccess.lean');s=p.read_text()
a=s.index('private theorem mapped_try_success');b=s.index('private theorem array_eq_false');s=s[:a]+s[b:]
start=s.index('    obtain ⟨pay, hpay, h⟩ :=');end=s.index('\n#print axioms',start)
prefix='validate_pool_v1_pair_forest_terminal_statement_v1.'
def branch(res,eq,var,cl,err,indent,body):
 i=' '*indent; inst=prefix+cl
 return f'''{i}obtain ⟨{res}, {eq}, h⟩ := bind_success _ _ _ h
{i}cases {res} with
{i}| Err e =>
{i}    obtain ⟨mapped, hmap, h⟩ := bind_success _ _ _ h
{i}    have hmap' : mapped = .Err (PoolV1PairForestTerminalFormatErrorV1.{err} e) := by
{i}      simpa only [core.result.Result.map_err,
{i}        {inst},
{i}        {inst}.call_once,
{i}        bind_tc_ok, Result.ok.injEq] using hmap.symm
{i}    subst mapped
{i}    obtain ⟨cf, hcf, h⟩ := bind_success _ _ _ h
{i}    have hcf' : cf = .Break (.Err (PoolV1PairForestTerminalFormatErrorV1.{err} e)) := by
{i}      simpa only [core.result.Result.Insts.CoreOpsTry.branch, Result.ok.injEq] using hcf.symm
{i}    subst cf
{i}    simp only [core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
{i}      core.convert.FromSame.from, bind_tc_ok] at h
{i}    cases h
{i}| Ok {var} =>
{i}    obtain ⟨mapped, hmap, h⟩ := bind_success _ _ _ h
{i}    have hmap' : mapped = .Ok {var} := by
{i}      simpa only [core.result.Result.map_err, Result.ok.injEq] using hmap.symm
{i}    subst mapped
{i}    obtain ⟨cf, hcf, h⟩ := bind_success _ _ _ h
{i}    have hcf' : cf = .Continue {var} := by
{i}      simpa only [core.result.Result.Insts.CoreOpsTry.branch, Result.ok.injEq] using hcf.symm
{i}    subst cf
{i}    dsimp only at h
'''+''.join(i+'    '+line+'\n' if line else '\n' for line in body.splitlines())
late='''split at h
· cases h
· rename_i hlaneEq
  have hlaneEq : lane = c.output_lane := by simpa only [bne_iff_ne, not_not] using hlaneEq
  subst lane
  obtain ⟨s, hslice, h⟩ := bind_success _ _ _ h
  have hslice' : s = Array.to_slice_mut (Array.repeat 1520#usize 0#u8) := by
    simpa only [lift, Result.ok.injEq] using hslice.symm
  subst s
  obtain ⟨⟨r, late⟩, hlate, h⟩ := bind_success _ _ _ h
  cases r with
  | Err e =>
      simp only [core.result.Result.map_err,
        validate_pool_v1_pair_forest_terminal_statement_v1.closure_3.Insts.CoreOpsFunctionFnOnceTuplePoolV1PairLatePublicStatementErrorV1PoolV1PairForestTerminalFormatErrorV1,
        validate_pool_v1_pair_forest_terminal_statement_v1.closure_3.Insts.CoreOpsFunctionFnOnceTuplePoolV1PairLatePublicStatementErrorV1PoolV1PairForestTerminalFormatErrorV1.call_once,
        bind_tc_ok, core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
        core.convert.FromSame.from] at h
      cases h
  | Ok u =>
      cases u
      exact ⟨pay, late, hpay,
        array_eq_false _ u8_ne_spec _ _ hm,
        array_eq_false _ u8_ne_spec _ _ hc,
        array_eq_false _ u8_ne_spec _ _ hs, hlane',
        array_ne_false _ u8_ne_spec _ _ hpool,
        array_ne_false _ u8_ne_spec _ _ hdeployment,
        array_ne_false _ u8_ne_spec _ _ hsnapshot,
        by simpa only [bne_iff_ne, not_not] using hsequence,
        array_ne_false _ m31_ne_spec _ _ hanchor, hlaneEval, hlate⟩'''
account=branch('r','hlaneEval','lane','closure_2.Insts.CoreOpsFunctionFnOnceTuplePoolV1PairForestAccountErrorV1PoolV1PairForestTerminalFormatErrorV1','Account',2,late)
body='''obtain ⟨view, hpublic, h⟩ := bind_success _ _ _ h
have hp : view = (p.pool, p.deployment_domain, p.anchor_sequence,
    p.anchor_root, p.nullifier, p.asset_id) := by
  simpa only [statement_public_common, Result.ok.injEq] using hpublic.symm
subst view
obtain ⟨hpool, h⟩ := bool_guard_success _ _ _ h
obtain ⟨hdeployment, h⟩ := bool_guard_success _ _ _ h
obtain ⟨hsnapshot, h⟩ := bool_guard_success _ _ _ h
split at h
· cases h
· rename_i hsequence
  obtain ⟨hanchor, h⟩ := bool_guard_success _ _ _ h
'''+account
s=s[:start]+branch('r','hpay','pay','closure_1.Insts.CoreOpsFunctionFnOnceTuplePoolV1PaymentStatementFormatErrorPoolV1PairForestTerminalFormatErrorV1','Payment',4,body)+s[end:]
p.write_text(s)
