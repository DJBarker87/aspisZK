from pathlib import Path
import json,collections
E=Path(__file__).resolve().parent
attempts=[json.loads(l)for l in (E/'NFU_ATTEMPTS.jsonl').read_text().splitlines() if l.strip()];counts=collections.Counter(x['kind'] for x in attempts)
closed=json.loads((E/'NFU_CLOSED.json').read_text());cf={f['function'] for f in closed['functions']}
scope=json.loads((E/'NFU_SCOPE.json').read_text())['members']
lines=['# NFU remaining assigned members (live handoff)','',f"Checked new closure: {closed['new_composed_functions']} functions / {closed['new_composed_rows']} D rows. Driver OPEN. Receipt counts: {dict(counts)}. No new unvalidated row is claimed.",'']
for f in scope:
 if f['function'] in cf:continue
 n=f['function'];reason='Needs its own frozen native Result/state/frame/ordered-effects packet, matched controls, model association, all callee domains and raw ax2; a CLOSED child alone is insufficient.'
 if n.endswith('::Accumulator::new'):reason='OPEN callee heap::filled is outside assigned members; see NFU_BOUNDARIES.md. Initialization model/native work cannot promote the caller without this allocation/value/error/frame packet.'
 elif n.endswith('::checkpoint'):reason='KNE schedule is a retained CLOSED local packet, but the actual reached-call DriverEstablishedDomain must be derived from SAME preparation/query-loop state; preparation is outside NFU and query-loop belongs to NFS. See NFU_BOUNDARIES.md; no free domain hypothesis is admitted.'
 elif n.endswith('::finish_query_dot'):reason='NFG EbyKDot::push is a CLOSED Q callee. Still needs one native iteration on arbitrary pre-state with exact field/weights arguments, full local-record reply/mutation/frame control, Lean loop induction, final new/finish association and caller-established push domains.'
 elif n.endswith('::check_values'):reason='One-chunk K007/K008 and pointer-iterator K030/K031 pass/fail; check_one needs exact KMX replay because CM31::from_le_bytes reaches try_into copies. Namespaced retained complete Scan proofs compile through L045; own wrapper and raw audit/admission pending.'
 elif n.endswith('::expand_values'):reason='Exact KMX copy16 K024/K025, local write/frame K026/K027 and guard K028/K029 pass/fail. Retained spatial/induction proofs retargeted coherently under NFU_Retarget through L045; generic full iterator association, wrapper and raw audit/admission pending.'
 elif 'OwnedAccount::key' in n or 'OwnedAccount::owner' in n or n.endswith('::require_readonly_buffer'):reason='Borrowed native pass/fail pairs K016..019 and K022/K023 plus L009 model/field-irrelevance laws are ready; raw ax2 and additive admission still required. K014/K020 timeouts excluded; no cleanup claim.'
 elif any(n.endswith('::'+t)for t in ['stage1','stage1_owned','stage2','stage2_owned']):reason='Decode/route composition must preserve exact arguments and abort/cleanup order. Transaction callees are outside this assignment; OPEN snapshot/authentication/validation/getter/observer dependencies must be cited, never assumed. No root promotion from a local routing check.'
 lines += ['## '+n,'','Rows: '+', '.join(f['rows'])+'. '+reason,'','Callees: '+('; '.join(c['function']+' ['+c['scope']+']'for c in f['callees'])or 'none')+'.','']
(E/'NFU_REMAINING.md').write_text('\n'.join(lines))
(E/'NFU_HANDOFF.md').write_text(f'''# NFU live handoff

Branch `codex/cx-slice-d-check-20261104`; receipts `evidence/slice-d-check-20261104/`.

Checked result: **{closed['new_composed_functions']} new composed functions / {closed['new_composed_rows']} D rows**; see NFU_CLOSED.json, NFU_CERTIFICATES.json and additive NFU_certify.py. D is 23/343 CLOSED at this checkpoint; driver remains OPEN. The deployed 100-bit per-attempt target is not yet established.

Committed stages: 3879c16c0d8 (scope/error callback), 08c43bb83e5 (record getters). Later work is pending audit/admission; never report it as closure. No push, merge, shipped source, session-A worktree, wallet/key or chain change.

Current receipt counts: {dict(counts)} out of 100 Kani / 60 Lean / 3 extraction. K014/K020 timed out and are excluded. K015/K021 were NOT launched; no timeout control is queued unchanged. L006/L008/L010/L013 failed and are excluded. Corrected model attempts are L007/L009; retargeted leaf modules L011/L012/L014..L045 pass. Their copied theorem terms are unchanged, imports are private, old global helpers live under NFU_Retarget and unused Phase aliases the canonical NFN owner. Explicit isize discriminant syntax is corrected to the selected canonical adapter. See NFU_RETARGET.json/.diff and NFU_BOUNDARIES.md.

Host workspace `/home/dombarker/project-offloads/codex-cx-slice-d-check-20261104`; retained private cache `/home/dombarker/project-offloads/codex-cx-slice-d-check-cache-20261104`. The cache is never deleted. Seed provenance/hashes are NFU_CACHE_IMPORTS.json.xz/.sha256; all 31 NFQ export hashes pass NFU_NFQ_CACHE_CHECK.json. Use the receipt's pinned LEAN_PATH and selected Aeneas objects. No source substitution from live sibling worktrees.

Each launch uses unchanged S2W_run_host.py, allowed:true AND exit0 admission, one own scope at a time, MemoryHigh6G/Max8G/Swap0/Tasks64; Lean -M7000, optimized offline Rust/Kani with frozen graph validation before every run and unchanged lock afterward. Exact per-attempt targets, exit, wall/RSS/swap/source/dependency/tool pins and axiom lines are in NFU_ATTEMPTS.jsonl and source snapshots. KMX patch is the adopted bcdf749b78eb6143789500d98d64ec3d407b8a17a6d1290c70c822473e8e9a67 patch; no private copy stub is written.

Next: finish namespaced compact leaf wrapper, KMX replay of check_one, full iterator/window and validator steps, raw audit, additive admission. Adapter getter/helper results await that same audit. Continue independent remaining members listed in NFU_REMAINING.md; do not stop on Kani exhaustion while Lean obligations remain. Preserve root physical/ABI/source-to-ELF/compiler/library/P6 option-A trust; RuntimePersistence/ReturnData/Memcmp and runtime digest realization remain accepted trust, never discharged here. Inherited ELF pins f8c0ec72..., 63ad3e9c..., 121f3e29... are not newly reproduced: no rebuild trigger has fired.
''')
