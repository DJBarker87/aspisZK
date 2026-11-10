#!/bin/bash
# PCXH_rename.sh: deterministic per-file rename rule on Stream C's own PRVEq evidence files (never shipped or Aspis source).
# Sources come from ../prov-p6v-20261110 (committed PCXG copies); renamed copies are written next to this script; every rename recorded in PCXH_RENAMES.json.
cd "$(dirname "$0")"
python3 -I -B - <<'PY'
import re, json, hashlib
S = '../prov-p6v-20261110/'
sha = lambda b: hashlib.sha256(b).hexdigest()
W = lambda t: r'(?<![A-Za-z0-9_])' + re.escape(t) + r'(?![A-Za-z0-9_])'
rules = {
 # rule R1: namespace PCVH of the k1 parser module clashes with PRVCmb_C19 (PCVH.dec_qm and 20 more names)
 'PRVEq_PCVH_R1CandidateWideParserSource_k1': [('PCVH', 'PCVH_k1')],
 'PRVEq_Op2_p5': [('PCVH', 'PCVH_k1')],
 # rule R2: namespace PCVK_S1 / PCVK_S2 / PCVK_C of the three o1 base modules (and their dependents) clash with PRVCmb_C20; the three PRVEq_ helper names and the delta_matchers tactic keyword clash between S1, S2 and C20
 'PRVEq_AdapterStage1_o1': [('PCVK_S1', 'PCVK_S1_o1'), ('PRVEq_after_ex', 'PRVEq_after_ex_s1'), ('PRVEq_usize_add_wrap', 'PRVEq_usize_add_wrap_s1'), ('PRVEq_partialEq_ne_default', 'PRVEq_partialEq_ne_default_s1'), ('delta_matchers', 'delta_matchers_s1')],
 'PRVEq_AdapterStage1DeployedNOC_o1': [('PCVK_S1', 'PCVK_S1_o1')],
 'PRVEq_NocStage1Compose_o1': [('PCVK_S1', 'PCVK_S1_o1')],
 'PRVEq_AdapterStage2_o1': [('PCVK_S2', 'PCVK_S2_o1'), ('PRVEq_after_ex', 'PRVEq_after_ex_s2'), ('PRVEq_usize_add_wrap', 'PRVEq_usize_add_wrap_s2'), ('PRVEq_partialEq_ne_default', 'PRVEq_partialEq_ne_default_s2'), ('delta_matchers', 'delta_matchers_s2')],
 'PRVEq_AdapterStage2DeployedNOC_o1': [('PCVK_S2', 'PCVK_S2_o1')],
 'PRVEq_CallerPrepTx1_o1': [('PCVK_C', 'PCVK_C_o1'), ('delta_matchers', 'delta_matchers_c1')],
 'PRVEq_CallerPrepTx1DeployedNOC_o1': [('PCVK_C', 'PCVK_C_o1')],
 'PRVEq_NocPrepTx1Compose_o1': [('PCVK_C', 'PCVK_C_o1')],
}
recs = []
for f, rs in rules.items():
    b = open(S + f + '.lean', 'rb').read(); t = b.decode(); per = []
    for old, new in rs:
        t, n = re.subn(W(old), new, t); per.append(dict(old=old, new=new, occurrences=n))
        assert n > 0, (f, old)
    nb = t.encode(); open(f + '.lean', 'wb').write(nb)
    recs.append(dict(file=f + '.lean', source=S + f + '.lean', sha256_before=sha(b), sha256_after=sha(nb), renames=per))
json.dump(dict(schema='PCXH_RENAMES/1', rule='token rename with identifier-boundary regex (no letter, digit or underscore on either side); applied only to Stream C PRVEq evidence files; no theorem statement changed, only declaration, namespace and tactic-keyword names',
               clashes_found_by='PCXH_L001 (PCXH_NAMES.lean: olean constNames scan of the 54 credited modules, PCXH_L001 receipt)', records=recs), open('PCXH_RENAMES.json', 'w'), indent=1)
print(len(recs), 'files')
PY
