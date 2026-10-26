"""Installed-entry table and remaining obligations; no security score."""
from pathlib import Path
import json,re
r=Path(__file__).resolve().parents[2];e=r/'docs/research/100bit-spend-path-20261013/evidence/prover-dict-20261026';p=r/'docs/research/v8-r0-zk-20261009/lean/R1Z'
x=json.loads((e/'inventory.json').read_text());fs=(p/'PDict_ResumeDictionary.lean').read_text();ts=(p/'PDict_FinalTypes.lean').read_text()
new=set(map(int,re.findall(r'^theorem op(\d+)_installed',fs,re.M)));typ=set(map(int,re.findall(r'^theorem type(\d+)_installed',ts,re.M)))
extra={17:'PDict_FileFlush',124:'PDict_VolatileCell',125:'PDict_OffpathBorrow',126:'PDict_OffpathBorrow',218:'PDict_CtConstructor',220:'PDict_CtUpdate'}
new |= set(extra)
assert len(new)==94 and len(typ)==25
old={z['id'] for z in x['functions'] if z['inherited_source_selected']};assert not new&old
rows=[]
for z in x['functions']:
 d=z.copy();i=d['id'];d['status']='new source interpretation' if i in new else 'inherited source interpretation' if i in old else 'OPEN'
 d['theorem']=f'R1Z.{extra.get(i,"PDict_ResumeDictionary")}.op{i}_installed' if i in new else None
 d['native_qualification']='P6 full primitive-field state/loan contract' if i in {19,20,21,24} else 'Source interpretation; native checks retain the scopes in native-summary.json and do not assert complete caller/effect adequacy'
 if i in {2,27,206,213,214,125,126,218,220}:d['native_qualification']='D188 exact extracted body; exact normalization/source pins in resume/; callbacks retain all outcomes'
 if i==211:d['native_qualification']='Generic Lean field flattening; P6 native association only at actual publication T=u8, every256-bit input and output index; no blanket all-Rust-T ownership/Drop law'
 if i==238:d['native_qualification']='P6 actual volatile32-byte cell zero and neighbor frame; no whole-Drop/order/fence contract'
 if i==13:d['native_qualification']='P6 value outcome partition plus pinned std match; no cross-thread/signal synchronization/reordering transport'
 if i==17:d['native_qualification']='P6 actual std File::flush for every nonnegative descriptor, success and owner value/frame preserved; OS ownership, close/Drop and world association remain explicit'
 if i==124:d['native_qualification']='P6 actual volatile mask-cell M31/QM31 instances, every input/replacement bit and neighboring frame; generic Lean value only, no arbitrary-Rust-T ABI/Drop, fence or temporal event transport'
 rows.append(d)
types=[]
for z in x['types']:
 d=z.copy();i=d['id'];d['status']='installed value/source representation' if i in typ else 'OPEN';d['theorem']=f'R1Z.PDict_FinalTypes.type{i}_installed' if i in typ else None
 d['support']='P6 complete signed32 value codec; no entropy/ABI/Drop composition' if i==7 else 'P6 complete64-bit float codec; no floating arithmetic interpretation' if i==26 else 'D188 transparent type extraction; existing std/Allocator Vec/Layout models where used' if i in typ else 'Native resource/dynamic representation and effect/frame association still needed; no standard-library axiom selected'
 types.append(d)
remaining=[z for z in rows if z['status']=='OPEN'];outside=[z for z in remaining if z['in_outer_overapprox'] and not z['in_body_overapprox']]
result=dict(selector='R1Z.PDict_FileFlush.selected',types='R1Z.PDict_FinalTypes.native',new_source_entries=len(new),source_selected_total=len(new|old),remaining_function_count=len(remaining),remaining_outside_body_overapprox=len(outside),native_type_interpretations=len(typ),remaining_types=[z['id'] for z in types if z['status']=='OPEN'],functions=rows,type_entries=types,root_premises_removed=0,unchanged_target='ProverCommitDeployedFuel22.RustProverRefinement conjunct1',remaining_root='Concrete PrefixContract/BodyContract; native entropy/ROM/TLS/IO/effect association; all-adversary/witness common finite-carrier RunJoin with both exact marginals and joint observer agreement off unchanged realBad, with unchanged independent seed.',qualification='Counts describe simultaneous lower source/value interpretations. They are not counts of headline premises discharged, nor an accepted native full dictionary or release certificate.')
(e/'installed-and-remaining.json').write_text(json.dumps(result,indent=2)+'\n')
lines=['# Installed and remaining prover dictionary entries','','Target not yet established. Zero root refinement premises removed. These tables describe the final simultaneous partial source/value dictionary.','',f'New source entries:{len(new)}; inherited:62; selected:{len(new|old)}/262. Remaining:{len(remaining)}, including{len(outside)} outer-reachable entries outside the proof-body reachability overapproximation. Type interpretations:25/28; remaining0,3,27.','','## Newly installed entries','','| ID | Name | Theorem |','|---:|---|---|']
for z in rows:
 if z['id'] in new:lines.append(f"|{z['id']}|`{z['name']}`|`{z['theorem']}`|")
lines+=['','## Type interpretations','','| ID | Name | Status and theorem |','|---:|---|---|']
for z in types:lines.append(f"|{z['id']}|`{z['name']}`|{z['status']}; `{z['theorem'] or 'no theorem'}`|")
lines+=['','## Remaining function entries','','Body-reachable entries remain with the sibling except the closed semantic-error equality. This syntactic overapproximation also includes error branches; it is not an honest-run restriction. Native implicit Drop reachability is not captured by this source reference scan.','','| ID | Name | In body overapproximation |','|---:|---|---|']
for z in remaining:lines.append(f"|{z['id']}|`{z['name']}`|{z['in_body_overapprox']}|")
lines+=['','All E1/E2, carrier, adversary, witness, bad-event, seed and observer requirements remain unchanged. File ownership and dynamic IO-error/formatter representations are open. No complete native dictionary, root RunJoin, privacy,100-bit or adoption claim is made.','']
(e/'ENTRIES.md').write_text('\n'.join(lines))
print({k:result[k] for k in ['new_source_entries','source_selected_total','remaining_function_count','remaining_outside_body_overapprox','native_type_interpretations','remaining_types','root_premises_removed']})
