#!/bin/bash
# PCXF_audit_l.sh: PCXF_AUDIT_L.json (audit scopes of the L187-universe deployed-top-body modules, by-reference imports) and PCXF_UNIVERSES.json.
cd "$(dirname "$0")"
python3 -I -B - <<'PY'
import json, re, os, lzma, collections
STD = {'propext', 'Classical.choice', 'Quot.sound'}
def log(a):
    p = f'{a}/stdout.log'
    return open(p).read() if os.path.exists(p) else lzma.open(p + '.xz').read().decode()
EXP = {
 'PCXF_L004': ['PCVS_Tx2Deployed.deployed_tx2_common_s', 'PCVS_Tx2Deployed.deployed_tx2_authenticated_s', 'PCVS_Tx2Deployed.e32_deployed', 'PCVS_Tx2Deployed2.yMix_eq', 'PCVS_Tx2Deployed2.deployed_tx2_common_m', 'PCVS_Tx2Deployed2.deployed_tx2_authenticated_m',
   'PCVS_E32.e32_core', 'PCVS_Eq.bind_mul', 'PCVS_Eq.bind_zero', 'PCVS_Eq.bind_one', 'PCVS_Op17.op17_frozen_bound', 'PCVS_Ckpt.tag_eq', 'PCVS_Ckpt.final_len_eq', 'PCVS_Ckpt.fixed_eq', 'PCVS_Ckpt.checkpoint_size_eq', 'PCVS_Ckpt.zeroK_eq',
   'PCVQ_Tx2Deployed6.leaves', 'PCVQ_Tx2Deployed6.h18', 'PCVQ_Tx2Deployed6.h18_deployed', 'PCVQ_Tx2Deployed6.deployed_tx2_common_q', 'PCVQ_Tx2Deployed6.deployed_tx2_authenticated_q', 'PCVQ_Resumeq13.resume_sim',
   'PCVQ_DeriveRef.deployed_qm31_clone', 'PCVQ_DeriveRef.we_clone_id', 'PCVQ_DeriveRef.qm31_eq_iff', 'PCVQ_DeriveRef.we_eq_iff', 'PCVQ_Tx2Deployedq5.anyLoop_eq', 'PCVQ_Tx2Deployedq5.leaf_any', 'PCVQ_Tx2Deployedq5.leaf_raw', 'PCVQ_Tx2Deployedq5.leaf_k', 'PCVQ_Tx2Deployedq5.leaf_filled',
   'PCVQ_Validate2.step', 'PCVQ_Validate2.loop_exact', 'PCVQ_Validate2.validate_fresh', 'PCVN_Op2.op2_frozen', 'PCVN_Tx2Deployed_n1.op2_deployed_frozen', 'PCVN_Op13.op13_frozen', 'PCVN_Op13.fresh_eq_gate', 'PCVN_Op17.post_eq', 'PCVN_Op17.powers_eq', 'PCVN_Op17.op17_frozen', 'PCVN_Tx2Deployed_n1.op3_deployed_shape',
   'PCVN_Tx2Deployed.deployed_tx2_common', 'PCVN_Tx2Deployed.deployed_tx2_authenticated'],
 'PCXF_L005': ['PCVP_S1.noc_model1', 'PCVP_S1Compose.fresh_stage1_iff'],
 'PCXF_L006': ['PCVP_S2.noc_model2'],
 'PCXF_L007': ['PCVP_C.noc_prepare', 'PCVP_C.noc_tx1', 'PCVP_C.seed_prepare', 'PCVP_C.noc_op1', 'PCVP_C.noc_op1_filled', 'PCVP_C.noc_op1_ne_div', 'PCVP_C.old_op1_div', 'PCVP_CComp.fresh_prepare_forward', 'PCVP_CComp.fresh_prepare_converse', 'PCVP_CComp.fresh_tx1_forward', 'PCVP_CComp.fresh_tx1_converse',
   'PCVP_NocSlots.cur_eq', 'PCVP_NocSlots.op3', 'PCVP_NocSlots.op4', 'PCVP_NocSlots.op5', 'PCVP_NocSlots.op7', 'PCVP_NocSlots.op16', 'PCVP_NocSlots.op17', 'PCVP_NocSlots.op19', 'PCVP_NocSlots.op20', 'PCVP_NocSlots2.op8', 'PCVP_NocSlots2.op10', 'PCVP_NocSlots2.op18']}
res = []; missing = {}; tot = 0; nonstd = {}
for a, names in EXP.items():
    rc = json.load(open(f'{a}/receipt.json')); t = log(a)
    ax = {}
    for n, rest in re.findall(r"^'([^']+)' (does not depend on any axioms|depends on axioms: \[[^\]]*\])", t, re.M):
        ax[n] = set() if rest.startswith('does') else {x.strip() for x in rest[rest.index('[') + 1:-1].replace('\n', ' ').split(',')}
    tg = re.search(r'PRVCMB_AUDIT_TARGETS (.*) (\d+)$', t, re.M); un = re.search(r'PRVCMB_UNION_AXIOMS \[([^\]]*)\]', t); cnt = re.search(r'PRVEQ_AUDIT_COUNT (\d+) skipped_by_time_guard=(\d+)', t); loc = re.search(r'PRVEQ_LOCAL_AXIOM_DECLS (\d+)', t)
    found = {}; miss = []
    for nm in names:
        h = [k for k in ax if k == nm or k.endswith('.' + nm)]
        if h: found[nm] = h[0]
        else: miss.append(nm)
    bad = {k: sorted(v - STD) for k, v in ax.items() if v - STD}
    res.append(dict(attempt=a, exit=rc['exit_status'], wall_seconds=round(rc['wall_seconds'], 1), peak_rss_kib=int(rc['peak_rss_kib']), swaps=rc['swaps'], target=rc['module'], source_sha256=list(rc['source_hashes'].values())[0], audit_targets=int(tg[2]), per_item_audited=int(cnt[1]), skipped_by_time_guard=int(cnt[2]),
                    union_axioms=un[1], local_axiom_decls=int(loc[1]), nonstandard=bad, n_expected_credited_names=len(names), n_found=len(found), missing=miss, found_as=found, errors=len(re.findall(r': error', t))))
    tot += int(cnt[1]); missing[a] = miss; nonstd.update(bad)
json.dump(dict(schema='PCXF_AUDIT_L/1', target_established=False, method='each audit module imports the credited modules by reference from the PCVN/PCVQ/PCVS/PCVP export directories (objects built by those jobs exit-0 scopes, chain in PCXF_LP_L1.json / PCXF_LP_L2.json) and audits by #print axioms every theorem whose name contains the job tag; not renamed bundles',
               scopes=res, total_theorems_audited=tot, all_expected_names_found=all(not m for m in missing.values()), nonstandard=nonstd), open('PCXF_AUDIT_L.json', 'w'), indent=1)
print('audit_l', tot, {a: (r['n_found'], r['n_expected_credited_names']) for a, r in zip(EXP, res)}, nonstd)
PY
