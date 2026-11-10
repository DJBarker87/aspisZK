import json,glob,os
notes={
'PCVD_L005':('probe: undrop WithdrawalCaller encode_common to see the instance-boundary error','Unknown identifier atomic_statement.encode_digest_canonical (cross-crate external absent in gate; gate has the local helper encode_digest_canonical)','transparent PCQE_E002 text inserted and proved equal to the gate helper (L009)'),
'PCVD_L006':('WC encode_*: fresh helper blocks inserted after their use','Unknown identifier at three use sites; prv_peel unknown (P3c WC file has no loop bridge)','insert before encode_common; inline the bridge'),
'PCVD_L007':('WC: loop-bridge theorem for the helper loop','gate encode_digest_canonical_loop is `loop`-based (body + loop), not partial_fixpoint: no fixpoint_induct; hpre goal unsolved','body, loop and wrapper as plain nonloop equalities (same text)'),
'PCVD_L008':('WC: encode_pool_v1_withdrawal_public_v1 by simp only','unsolved goal: sides print identical, differ only by match/destructuring-let encoding','finish with rfl after simp only'),
'PCVD_L013':('probe: print gate field.reduce_u64 / M31.reduce_u64 / reduce_u62 in AspisR1SelectedMaskProbe','reduce_u62 is not in the gate Funs (expected; probe only)','gate reduce_u64/M31.reduce_u64 exist, text-identical to fresh (checked +)'),
'PCVD_L015':('Qm31PackBase4: callee equalities then qm31_pack_base4','alternatives all failed: simp only closes syntactically-equal sides except match-vs-let-destructure; with_reducible rfl cannot see it','added an `simp only [...]; rfl` alternative to the nonloop template (L017)'),
'PCVD_L016':('Qm31PackBase4 debug copy (single simp-only alternative)','same unsolved goal','as above'),
'PCVD_L020':('PreparedSum3: callee equalities against AspisR1PoseidonPreparedSum3Source.field.X','Unknown constant: the gate module opens AspisR1SelectedMaskProbe and defines only closure/karatsuba/loops','absolute gate names via GNAME with a leading ! (gq); fresh text from the P2g file (it contains the loops)'),
'PCVD_L022':('BatchedWeightsExtraction M31.reduce_u64 undropped as is','Unknown identifier field.M31 / gate name is aspis_core.field.M31.reduce_u64','name-map alias abbrev field.M31 + absolute gate name'),
'PCVD_L023':('probe: gate names of AspisR1BatchedWeightsExtraction','probe only','gate names carry the aspis_core. prefix'),
'PCVD_L025':('Native02 qm31_sum_products3_prepared with its fresh loops inserted but no loop equalities','rfl failed: callee fresh loop0 distinct from gate loop0','loop-bridge equalities for the three loops added first (L026)'),
}
rows=[]
for r in sorted(glob.glob('PCVD_L[0-9][0-9][0-9]/receipt.json')):
    d=json.load(open(r))
    if d['exit_status']==0: continue
    a=d['attempt']; n=notes.get(a,('','',''))
    rows.append(dict(attempt=a,target=d['module'],exit=d['exit_status'],wall_s=round(d['wall_seconds'],1),peak_rss_kib=d['peak_rss_kib'],shape=n[0],failure=n[1],replacement=n[2]))
with open('PCVD_FAILED_SHAPES.jsonl','w') as f:
    for x in rows: f.write(json.dumps(x)+'\n')
print(len(rows),[x['attempt'] for x in rows if not x['shape']])
json.dump(dict(schema='PCVD_TOOLS/1',
 inherited='PCVC_ tools copied and renamed (PCVD_run.py, PCVD_run_host.py: Stream C share < 2, host < 6, disk >= 40 GB, reservation barrier, 6G/8G swap 0, 180 s, -M7000, ledger30 PATHS); PRVC_LoopBridge.lean unchanged',
 changes=[
  dict(id='PCVD-1',file='mkbase.py',content='UNDROP (restore named PRV-FRESH-DROPPED blocks) and SHIMS (constant-binding defs inserted after `namespace PRVFresh_*`)'),
  dict(id='PCVD-2',file='gen_loops.py',content='HOIST (fresh loop with leading hoisted constant parameters: statement `@fresh (gate const) = @gate`), GNAME/gq (fresh->gate name map, `!` = absolute gate name)'),
  dict(id='PCVD-3',file='gen_p3.py',content='SHIMNAMES unfolded in nonloop proofs, nonloop alternative `simp only [...]; rfl`, nonloop_simp (simp-first, no with_reducible rfl, for heartbeat-limited bodies), multi-line `def\\n  name` recognised'),
  dict(id='PCVD-4',file='ext.py',content='extend an existing P2f/P2g/P3 file: undrop, insert transparent fresh blocks, generated theorems (loop / nonloop / simp)'),
  dict(id='PCVD-5',file='gen_d1.py gen_d13.py gen_wc.py gen_p23.py gen_nom.py gen_hb.py gen_ps3.py gen_bw.py gen_n02.py gen_n07b.py',content='per-module drivers; gen_d13.py slices the Native13 fresh section (COPY_PATTERNS literal replaced by a leading parameter)'),
  dict(id='PCVD-6',file='runl.sh showl.sh errsl.sh proved.py check_sources.py final_d.py final2_d.py final3_d.py listdropped.py showdef.py undrop.py',content='bash drivers and status writers'),
  dict(id='PCVD-7',file='PRVD_ConstBind.lean',content='generic constant-binding lemmas (const_bind, const_bind_of_eq, hoisted_param_eq, const_bind_unique)')],
 lean_policy='no raised heartbeats (file default 1000000 only; nonloop lowered to 100000, WC encode_* 400000); only propext, Classical.choice, Quot.sound'),open('PCVD_TOOLS.json','w'),indent=1)
