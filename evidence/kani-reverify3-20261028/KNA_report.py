"""Render terminal disposition from immutable receipts and exact uncredited intervals."""
from pathlib import Path
import json,collections
E=Path(__file__).resolve().parent
runs=json.loads((E/'KNA_RUNS.json').read_text());rows=json.loads((E/'KNA_ROW_CREDITS.json').read_text());pairs=json.loads((E/'KNA_PAIRS.json').read_text())
c=collections.Counter(r['kind'] for r in runs);results=collections.Counter(r['result'] for r in runs if r['kind']=='kani')
final=json.loads((E/'KNA_L040/receipt.json').read_text())
order=['LPe_K017','LPf_K027','LPi_K017','LPi_K018','LPm_K003','LPm_K004','LPm_K005','LPi_K012','LPi_K013']
assert all(rows[r]['status']=='OPEN' for r in order),'Review new credit before rendering report'
lines=['# KNA checkpoint/append finding','', '**0 newly CONFIRMED, 0 FAILED, 9 OPEN. Checkpoint/append leaf credit: KEEP SUSPENDED.**','',
'The disk-full stop was resumed after the lead restored space. K014 was checked read-only on the host: its terminal receipt agrees with the retained local receipt, and no KNA job was live. No submitted attempt was resubmitted. Historical stop details remain in [KNA_INFRASTRUCTURE_STOP.json](KNA_INFRASTRUCTURE_STOP.json).', '',
f'**Budget used: Kani {c["kani"]}/90, Lean {c["lean"]}/40, optimized Rust {c["rust"]}/5.** Kani classifications: '+', '.join(f'{n} {k}' for k,n in sorted(results.items()))+'. No timeout or unrun child earns heap credit. The seven previously confirmed KMZ rows retain their authoritative disposition; checkpoint remains 3/12 restored.','',
'## Per-row disposition and exact next splits','',
'Every row remains OPEN for the runtime obligations below. The original assertion has not been falsified; there is no original-property counterexample requiring replay. All new gates use the exact KMX definitions and a matched XOR1 control. The gate and receipt lists, including every uncredited interval and its next halving, are in [KNA_ROW_CREDITS.json](KNA_ROW_CREDITS.json).','',
'| Original row | Result, completed gates and exact next work |','|---|---|']
for row in order:
 r=rows[row]
 if row in ['LPf_K027','LPi_K017','LPi_K018']:
  groups=[]
  for x in r['remaining']:
   groups.append(f'`[{x["range"][0]},{x["range"][1]})` '+x['status']+' → '+', '.join(f'`[{a},{b})`' for a,b in x['next_split']))
  text='**OPEN.** Shared actual Vec::from(array1736), append32, cap1736→3472. Uncredited leaves and exact next replacements: '+'; '.join(groups)+'.'
  if row=='LPf_K027':text+=' Lean L035 reconstructs checksum byte/length/call relation.'
  elif row=='LPi_K017':text+=' Lean L036 retains both root replacements, three calls, length1768 and joined-byte formula; prior oracle evidence supplies proof/public sizes3/5.'
  else:text+=' Lean L037 retains the same joined-byte relation; KMY_K037 supplies physical proof/public arguments57607/1880.'
 elif row=='LPe_K017':
  text='**OPEN.** Actual constructors/truncation retained. '+ '; '.join('`'+x['name']+'` '+x['positive']+'/'+x['control']+' ('+x['positive_id']+'/'+x['control_id']+')' for x in r['gates'] if x)+'. '+r['next']+' Query models L027/L028 and original roots/query formula L034 pass.'
 else:
  text='**OPEN.** '+r['domain']+'. '+ '; '.join('`'+x['name']+'` '+x['positive']+'/'+x['control']+' ('+x['positive_id']+'/'+x['control_id']+')' for x in r['gates'])+'. '+r['next']
  if row=='LPm_K003':text+=' Retain the same selected shared reference and actual put_k call.'
  if row=='LPm_K005':text+=' Retain the original u32 little-endian shift/byte formula.'
  if row=='LPi_K012':text+=' Retain the original qbytes auxiliary contract and scalar16 byte projection.'
  if row=='LPi_K013':text+=' Retain canonical WideExact auxiliary serializer scope and eight-limb byte projection.'
 lines.append('| '+row+' | '+text+' |')
lines += ['', '## Lean composition and native corroboration','',
'38 focused modules and the single final manifest pass. L001 failed on the reserved binder `prefix`; L002 compiles its renamed replacement. The failed source is archived by hash. The redundant standalone capacity audit was excluded from the final manifest to preserve the 40-attempt budget; query capacity domains and growth premises remain in the focused row modules. KNA_Capacity.lean is **UNRUN**.', '',
f'**KNA_L040 / KNA_Final.lean PASS:** exit{final["exit_status"]}; wall {final["wall_seconds"]} s; peak RSS {final["peak_rss_kib"]} KiB; swaps{final["swaps"]}; execution source revision `{final["source_revision"]}`; target SHA-256 `{final["source_hashes"]["KNA_Final.lean"]}`. All38 printed top-theorem audits use only propext, Classical.choice and Quot.sound. [Receipt](KNA_L040/receipt.json), [axioms](KNA_L040/stdout.log).', '',
'The symbolic frame, eleven-prefix-plus-tail partition, half-window union, query domains and nine row projections compose the retained KMY/KMZ/KMX value laws. Successful allocation, initialization and heap-frame facts are separate runtime obligations. These Lean models receive no missing heap credit.', '',
'Optimized native R001–R005 pass: all20 query cases, full1736→1768 body transition, all64 selected-reference cases, append16 lengths0..1720, and append32/append4 lengths0..1704/1732. Each checks the correct relation and a concrete XOR1 inequality. R002 also invokes the unchanged KMX_realloc on initialized bytes. Native allocation uses the native allocator; these runs corroborate witnesses and do not replace symbolic Kani coverage.', '',
'## Frozen scope, controls, resources and reproducibility','',
'Frozen Rust revision: `4bb3b3f51e16b4525f1d10336e2b0bcbbd775387`. Frozen Cargo.lock SHA-256: `5782e6a32026fdd95d252d0db7ea20b16716e6deb4f5a397e744886bb6ba22ef`. KMX patch SHA-256: `bcdf749b78eb6143789500d98d64ec3d407b8a17a6d1290c70c822473e8e9a67`. Exact KMX stub file SHA-256: `c282a1272676cd56fd2702f60b17009bac9d252e495b1508459b01d6ed1cf9d9`.', '',
'Every new receipt records both KMX hashes. No new copy stub was written. Within each positive/control pair, the domain, source definitions, unwind, optimized profile, solver and auxiliary scope match; only the selected expected byte changes by XOR1. [KNA_PAIRS.json](KNA_PAIRS.json) records credit. A timeout on either side supplies no credit under ruling (r\').', '',
'The existing scratch crate and copied frozen lock were reused. Every Kani/native gate validates the resolved package/edge graph against the frozen lock before invocation, uses CARGO_NET_OFFLINE=true and opt-level3, and confirms the lock hash unchanged afterwards. No release source under crates/ or programs/ was changed.', '',
f'[KNA_RUNS.json](KNA_RUNS.json) indexes all{len(runs)} immutable receipts with exact command, exit status, wall time, peak RSS, swaps, source revision/hash and axioms. Maximum reported RSS: {max(r["peak_rss_kib"] for r in runs)} KiB; all swaps0. Every admitted scope enforced MemoryHigh6G, MemoryMax8G, MemorySwapMax0, TasksMax64; one own scope at a time. Admission required allowed:true **and exit0**. Barrier/transport logs retain retries; no refusal was bypassed.', '',
'Changed Lean sources passed generator --check before compilation. No large concrete recurrence was normalized, no final manifest was repeated, and no timeout was rerun unchanged. [Source archive](KNA_SOURCE_ARCHIVE.json), [frozen pins](KNA_FROZEN.json), [resume record](KNA_RESUME.json), [cleanup](KNA_CLEANUP.json).', '',
'The persistent cache `/home/dombarker/project-offloads/codex-cx-kmy-cache-20261028` is retained. Attempt-owned temporary files and native binary are cleaned at completion; shared/unattributed files are retained. No wallet/key operation, external message, push or out-of-scope tracked edit occurred. File-size and disk checks are recorded at the final audit.']
(E/'KNA_FINDING.md').write_text('\n'.join(lines)+'\n')
