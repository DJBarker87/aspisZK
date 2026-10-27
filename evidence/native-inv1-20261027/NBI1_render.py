#!/usr/bin/env python3
import json,collections
from pathlib import Path
O=Path(__file__).parent
x=json.loads((O/'NBI1_INVENTORY.json').read_text());fs=x['functions'];model_ids={n:f'M{i:03}' for i,n in enumerate(sorted(x['models']),1)}
byid={f['id']:f for f in fs}
def esc(s):return str(s).replace('|','&#124;').replace('\n',' ')
def code(s):return '`'+esc(s)+'`'
lines=[(O/'NBI1_REPORT_HEADER.md').read_text()]
lines+=['## No separate counterpart: complete row list\n','| Unit | Functions (exact source pins in the function table) |','|---|---|']
groups=collections.defaultdict(list)
for f in fs:
 if not f['cohort_definitions']:groups[f['bridge_unit']].append(f)
for u,rs in sorted(groups.items()):lines.append('|'+u+'|'+', '.join(f['row']+' '+code(f['name']) for f in rs)+'|')
lines+=['\n## Proposed bridge units, bottom-up\n','S/M/L are engineering sizing only, not measured prover runtimes. Each unit lists its member rows and callee bridges. Its domain is what the caller must establish; callee-domain obligations in JSON point to these same domains. Small helpers and inline callbacks are merged with the indicated caller. CLOSED leaf units retain their packet domains. No unit in this table is newly proved.\n','| Order | Unit / size | Members | Callee bridges | Required domain |','|---|---|---|---|---|']
for u in x['bridge_units']:
 lines.append('|'+str(u['bottom_up_group'])+'|'+code(u['id'])+' '+u['estimate']+' — '+u['title']+'|'+', '.join(u['members'])+'|'+', '.join(u['callee_bridges'])+'|'+esc(u['domain'])+'|')
lines+=['\n## Every inventoried function\n','Callees are row IDs; a stopped leaf can also have internal targets outside this inventory, retained verbatim in JSON. Standard-library/runtime calls and inline callbacks are in each row\'s JSON call-site list. “Loop” lists explicit loop lines; I marks iterator combinators; B marks mutable signature/borrows; F names field calls; O names direct digest calls. Indirect callee effects compose through the listed edges. Body hashes are full SHA256. Cohort IDs resolve to exact Lean names/modules below; an empty cohort is explicitly “no cohort counterpart”.\n','| Row / function | Frozen file:line | Body SHA256 | Callees | CLOSED leaf | Cohort | Loops / borrows / field / oracle | Unit |','|---|---|---|---|---|---|---|---|']
for f in fs:
 targets=sorted(set(byid[t]['row'] for e in f['callees'] for t in e['targets'] if t in byid))
 flags=[]
 if f['loops']:flags.append('Loop '+','.join(str(l['line']) for l in f['loops']))
 if f['iterator_operations']:flags.append('I')
 if f['mutable_signature'] or f['mutable_borrows']:flags.append('B '+','.join(str(b['line']) for b in f['mutable_borrows']))
 if f['field_arithmetic']:flags.append('F '+','.join(sorted(set(c.rsplit('.',1)[-1] for c in f['field_arithmetic']))))
 if f['oracle_digest_calls']:flags.append('O '+','.join(f['oracle_digest_calls']))
 lines.append('|'+f['row']+' '+code((f['owner']+'::' if f['owner'] else '')+f['name'])+'|'+code(f['file']+':'+str(f['line']))+'|'+code(f['body_sha256'])+'|'+','.join(targets)+'|'+('yes' if f['closed_leaf_packet'] else 'no')+'|'+(','.join(model_ids[r['name']] for r in f['cohort_definitions']) or 'no cohort counterpart')+'|'+esc('; '.join(flags) or 'none')+'|'+f['bridge_unit']+'|')
lines+=['\n## Exact cohort declaration index\n','Module ownership is the retained replay audit\'s recorded owner; local source filenames may be import-only copies. Every name here occurs in RPx\'s actual dependency closure. Full source hashes, inherited audit references and replay-tops3 membership are in JSON. These are model definitions, not newly asserted Rust equalities.\n','| Model | Lean name | Replayed module | Located source |','|---|---|---|---|']
for n in sorted(x['models']):
 r=x['models'][n];lines.append('|'+model_ids[n]+'|'+code(n)+'|'+code(r['module'])+'|'+code(str(r['source'])+':'+str(r['line']))+'|')
lines+=['''
## Validation, receipts and retained boundaries

No Lean compile (0/30), Kani run (0), Rust execution/build (0), SBF rebuild or
frozen-manifest replay was launched. No new top theorem exists; `#print axioms`
is N/A for this job. The retained replay declaration audits are reused evidence,
not new kernel checks. No host scope, admission attempt, shared workspace,
Aeneas library object, persistent cache or session A file was touched; therefore
no host/cache start/end mutation or reservation receipt exists. No shipped file
or cfg(kani) harness changed; the ELF rebuild trigger did not fire. No hash is
claimed newly reproduced.

Inherited pins:

- default `f8c0ec72621fd5029a97d796c4a3623d0dc44a8e7074122372f9872915d143d4`
- devnet `63ad3e9cc096dcbb55b3ca7ac7c8e89e6a845796ab5e4f5b7d15db96f3784299`
- Pool `121f3e29741f510e6dc42d0345fc3c36217600f0be337094855c4a9da2581548`

`NBI1_VALIDATE.json` and `NBI1_validation-time.txt` record exact static target,
exit, wall, peak RSS, swaps, worker/source revisions, source/closure hashes and
axioms N/A. `NBI1_validate.py` independently rehashes every selected frozen
span, checks all model names and owner receipts,13 leaf boundaries, callee
coverage and bottom-up ordering. These checks validate this inventory; they
are not formal source-to-model refinement. `NBI1_SOURCE_FILES.json` seals the
270 inspected file hashes. The rest of crates/programs/Cargo.lock is also
checked byte-identical to the frozen revision by git diff.

The Python inventory parser uses tree-sitter0.25.2 / tree-sitter-rust0.24.2.
An initial tree-sitter0.26 parser segfault and one diagnostic rerun led to that
parser version pin; no prover was involved. A slow first cohort scan was stopped
and replaced with a stricter scan keyed to retained modules plus canonical Lean
sources. Own assembler defects (forward unit reference, audit count versus list)
were repaired before validation. The first independent validation found an unresolved private-Q callee inside the stopped Dot.push leaf; its owner was made explicit and the failed receipt is retained as NBI1_validation-failed1-*.txt. No failed script result is credited as evidence.
Intermediate AST/cohort indices are reproducible scratch outputs, not retained
proof caches. The stage2 call graph is superseded by NBI1_INVENTORY.json.

Exact claim: a frozen-source static TX1 inventory and cohort-name/owner mapping,
plus proposed bridge cuts and domains. Assumptions discharged/added/changed:
none. Existing library, runtime/ABI, allocator, extraction, digest/oracle,
query-budget and source-to-ELF boundaries remain. This does not close enclosing
S2, D188 caller association or the100-bit target. The next concrete work is the
native release-dispatch/snapshot/decoder-to-owned wrapper bridge, followed
bottom-up by parser/prepare/batch/query/flush domain composition into the SAME
checkpoint writer. Every CLOSED leaf is reused within its existing domain.

All stage commits are local; no push, merge, key/wallet operation, other worker
prefix edit or compiler/cache cleanup occurred.
''']
(O/'NBI1_INVENTORY.md').write_text('\n'.join(lines).rstrip()+'\n')
print('Rendered',len(fs),'functions,',len(model_ids),'cohort names')
