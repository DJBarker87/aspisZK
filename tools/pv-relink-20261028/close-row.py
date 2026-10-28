from common import *
import sys
row,label,attempt=sys.argv[1:];assert row in ['V178','V179','V182','V195','V233']
r=E/row/'row.json';j=json.loads(r.read_text());p=E/attempt/'receipt.json';proof=json.loads(p.read_text());native=E/label/'receipt.json';n=json.loads(native.read_text());log=(native.parent/'output.log').read_text()
assert proof['exit']==0 and n['exit']==0 and 'finite validation:' in log and 'no disagreement' in log
source=R/'docs/research/v8-r0-zk-20261009/lean/R1Z'/('PV_RL_'+row+'.lean');assert sha(source.read_bytes())==proof['sha256']
assert all('sorryAx' not in a for a in proof['axioms'])
j['after']['status']='RELINKED at prior candidate scope';j['native_receipt']=label+'/receipt.json';j['focused_proof_receipt']=attempt+'/receipt.json';j['finite_validation']=re.findall(row+r' finite validation:[^\n]+',log)[0];j['reverify_with_announced_validated_copy_stub']='Required under ruling(k\u2032) when announced; not performed here (Kani budget0).'
r.write_text(json.dumps(j,indent=2)+'\n')
(E/row/'RESULT.md').write_text(f'''# {row}: structural (K-1 substitute)

**Re-linked at the prior candidate value scope. Target not yet established.**

Before: {j['before']['residual']}

After: the suspended native link is replaced by the checked structural binding
`../{row}-binding.json`, the complete Result/reference law and its Lean transport,
and a same-input native differential explicitly classified as **finite validation**.
Retained residual: {j['after']['residual']}

Closing theorem (unchanged): `{j['closing_theorem']}`.
Focused proof / standard-axiom receipt: `../{attempt}/receipt.json`.
Native evidence: `../{label}/receipt.json`; {j['finite_validation']}.
Non-vacuity: `{j['non_vacuity']}`.

Historical Kani output and receipt blobs remain in `suspended-support.json` and
`suspended-*` files. Every such PASS is **suspended** and supplies **no native-link
credit**. No Kani solver was run; no copy stub was installed.

No quantifier, carrier, failure event or closing statement was weakened. No
canonical endpoint/deployment premise was removed or added. The bounded native
scope is unchanged even where the fresh finite corpus tests more cases. T remains
exactly entropy_law, entropy_kernel and observation. Native world/allocator,
compiler and deployed-closure limits remain as recorded above.
''')
print(row,'re-linked at prior candidate scope')
