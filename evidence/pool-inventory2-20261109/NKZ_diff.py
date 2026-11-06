"""New/old inventory comparison and dispatch review; read-only evidence producer."""
from pathlib import Path
import json,hashlib,subprocess,collections,lzma,re
E=Path(__file__).resolve().parent;R=E.parents[1];O=E.parent/'pool-inventory-20261109'
F='b936275465600469312d1f058cdc91ea2a11f3dc';C='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387';sha=lambda b:hashlib.sha256(b).hexdigest()
def load(p):return json.loads(p.read_text())
def put(n,d):(E/n).write_text(json.dumps(d,indent=1,sort_keys=True)+'\n')
def md(n,s):(E/n).write_text(s)
a=load(O/'NKS_INVENTORY.json');b=load(E/'NKZ_INVENTORY.json');old={r['function']:r for r in a['rows']};new={r['function']:r for r in b['rows']}
ot=load(O/'NKS_TRACTABILITY.json');nt=load(E/'NKZ_TRACTABILITY.json');oc={r['function']:r for r in ot['rows']};nc={r['function']:r for r in nt['rows']}
removed=[dict(old_row=old[k]['id'],function=k,frozen_body_sha256=old[k]['frozen_body_sha256'],class_=oc[k]['class_'],genuinely_new=old[k]['genuinely_new']) for k in sorted(set(old)-set(new))]
retained=[dict(old_row=old[k]['id'],new_row=new[k]['id'],function=k,old_body_sha256=old[k]['frozen_body_sha256'],new_body_sha256=new[k]['frozen_body_sha256'],body_identical=old[k]['frozen_body_sha256']==new[k]['frozen_body_sha256'],class_identical=oc[k]['class_']==nc[k]['class_']) for k in sorted(set(old)&set(new))]
assert not set(new)-set(old);assert len(removed)==216;assert all(x['class_identical'] for x in retained)
ob=load(O/'NKS_OBLIGATIONS.json');nb=load(E/'NKZ_OBLIGATIONS.json')
def compare(kind):
 n={x['function']:x for x in nb[kind]}
 return [dict(function=x['function'],old_row=x['row'],old_scope=x['scope'],new_row=n[x['function']]['row'] if x['function'] in n else None,new_scope=n[x['function']]['scope'] if x['function'] in n else None,disposition='RETAINED OPEN' if x['function'] in n else 'REMOVED SOURCE; not proved or promoted') for x in ob[kind]]
owners=compare('exclusive_guard_owners');held=compare('held_sites')
counts={k:dict(old=ot['new_on_counts'][k],new=nt['new_on_counts'][k],removed=sum(x['class_']==k and x['genuinely_new'] for x in removed)) for k in 'ABCD'}
assert all(v['old']-v['new']==v['removed'] for v in counts.values())
root=load(E/'NKZ_ROOTS.json');oldroot=load(O/'NKS_ROOTS.json');magics={x['magic'] for x in root['roots']};removedroots=[dict(**x,disposition='REMOVED: now InvalidInstructionData; no native proof credit') for x in oldroot['roots'] if x['magic'] not in magics]
put('NKZ_DIFF.json',dict(old_counts=a['counts'],new_counts=b['counts'],new_class_counts=counts,removed_on_rows=removed,retained_rows=retained,added_on_rows=[],removed_instructions=removedroots,guard_owner_dispositions=owners,held_site_dispositions=held,shared_basis_statuses_changed=False,proof_credit=0,security_target_established=False))
s='''# New Pool difference from NKS_

Target not yet established. Scope reduction only; no proof, status promotion, trust change or ledger edit.

Old freeze4bb3b3f5 / ELF121f3e29…; new Pool freeze b936275465600469312d1f058cdc91ea2a11f3dc / ELF e0e49c344d35575116c0359450315ea4334bfb03006551727f67c04a8cfe09dc. Crates remain4bb3b3f5. Same NKS_/NGB_ method and conservative alternatives; only source/compiler pins, removed-root handling and reports retargeted. NKZ_DIFF.json lists every removed row and old/new retained ID.

| Count | NKS | NKZ | Removed |
|---|---:|---:|---:|
| ON source occurrences | 613 | 397 | 216 |
| New to599-row basis | 494 | 278 | 216 |
| Shared body occurrences | 119 | 119 | 0 |
| Basis rows matched | 183 | 183 | 0 |
'''
for k,v in counts.items():s+=f"| New class {k} | {v['old']} | {v['new']} | {v['removed']} |\n"
s+='''
All397 retained functions have the same class.396 retained bodies are byte-identical; only processor::process_instruction changes (seven legacy arms removed). No function is added to the ON closure. Removed rows are listed below; none is labelled CLOSED by deletion.

Seven removed dispatch alternatives: ASIN (old OFF), ASDI/ASPT/ASWD/ASPP/ASPF/ASPX (old ON). Seven source alternatives remain: AS8C/AS8D/ASQ8 ON; AS8I and cfg-disabled ASF8/ASJP/ASJW OFF. No prepared/cancel/settle legacy root remains, and there is no standalone admin/registry/close instruction.

| Original exclusive guard owner | Old row / scope | New disposition |
|---|---|---|
'''
for x in owners:s+='| `'+x['function']+'` | '+x['old_row']+' '+x['old_scope']+' | '+(x['new_row']+' '+x['new_scope']+' OPEN' if x['new_row'] else 'REMOVED SOURCE')+' |\n'
s+='\n13→6 original guard owners:7 removed,3 ON and3 OFF retained;0 newly proved.\n\n| Held CPI/callback owner | Old row / scope | New disposition |\n|---|---|---|\n'
for x in held:s+='| `'+x['function']+'` | '+x['old_row']+' '+x['old_scope']+' | '+(x['new_row']+' '+x['new_scope']+' OPEN' if x['new_row'] else 'REMOVED SOURCE')+' |\n'
s+='''
Four held sites→three: legacy transition before_persist callback removed; pair deposit and terminal stay ON; cfg-disabled pair withdrawal stays OFF. RuntimeCpiReadonlyEntry7 remains pending and unused. Accessor sites21→15; all seven data_is_empty source sites remain, so the K086 nullifier-classifier family is not removed. Its native production reachability/exclusion remains UNPROVED (liveness/abort).

Revised estimate (not a measurement): A/B/C248 rows at the successful predecessor-helper sensitivity of1–2 rows/job gives124–248 predecessor-sized job-slots (was219–437 for437 rows). This is not established driver throughput; no finite empirical upper bound. D30 rows (was57) retain separate unbounded uncertainty. The surviving prefix-to-CPI and P1..P4 producers remain OPEN; removal does not decide owner option A/B.

| Removed ON occurrence | Class | Frozen function |
|---|---|---|
'''
for x in removed:s+='| '+x['old_row']+' | '+x['class_']+' | `'+x['function']+'` |\n'
md('NKZ_DIFF.md',s)
# Dispatch evidence is from the frozen source and actual deployed command.
source=subprocess.check_output(['git','show',F+':programs/aspis-pool/src/processor.rs'],cwd=R,text=True);lines=source.splitlines();entry=next(i for i,l in enumerate(lines,1) if l.startswith('pub fn process_instruction('));macro=next(i for i,l in enumerate(lines,1) if 'entrypoint!(process_instruction)' in l)
cmd=load(E/'NKZ_aspis_pool.command.json');features=sorted(cmd[i+1].removeprefix('feature="').removesuffix('"') for i,x in enumerate(cmd) if x=='--cfg' and cmd[i+1].startswith('feature='))
s=f'''# New release Pool instruction roots

Target not yet established. Pool source {F}; crates {C}. SDK entrypoint! is processor.rs:{macro}; process_instruction starts:{entry}. Exact SBF command and feature list are retained in NKZ_aspis_pool.command.json/NKZ_DEPLOYED_BUILD.json. Features: {', '.join(features)}.

ON is the conservative spend/lifecycle union, not a claim that all roots execute in one two-transaction trace. AS8C is retained conservatively for checkpoint preparation. Four dispatcher alternatives are active; three optional source alternatives are cfg-disabled. Every OFF alternative is shown for owner review.

| Magic | ON/OFF | Source root and line | Reason |
|---|---|---|---|
'''
for x in root['roots']:s+='| '+x['magic']+' | '+x['classification']+' | `'+x['function']+':'+str(x['source_line'])+'` | '+x['reason']+' |\n'
s+='\nRemoved alternatives (no dispatch arm; source fallback returns InvalidInstructionData):\n\n| Magic | Former class | Former root | New disposition |\n|---|---|---|---|\n'
for x in removedroots:s+='| '+x['magic']+' | '+x['classification']+' | `'+x['function']+'` | REMOVED; rejects |\n'
s+='\nNo standalone admin, registry-maintenance or close instruction remains. Short/unknown inputs reject; return data is cleared initially and on errors. The native/SBF difference is explicit: the transaction-level stack-height check is Solana-only, while native cfg excludes that syscall gate; the source magic/feature dispatch is otherwise the same. Tests are cfg(test), not deployed roots. Generic ASJP/ASJW bodies present in MIR do not establish production reachability; OFF edges and owners remain visible. SDK macro/allocator/panic/derives/std/external calls are boundary records, under NGB source-occurrence semantics.\n'
md('NKZ_ROOTS.md',s)
cfg=[]
for p in load(E/'NKZ_DEPLOYED_BUILD.json')['compiler_input_checks']:
 if not p['path'].startswith('programs/aspis-pool/') or not p['path'].endswith('.rs'):continue
 body=subprocess.check_output(['git','show',F+':'+p['path']],cwd=R,text=True)
 cfg.extend(dict(file=p['path'],line=i,text=l.strip()) for i,l in enumerate(body.splitlines(),1) if 'cfg' in l and any(t in l for t in ['target_os','feature','test']))
put('NKZ_CFG_REVIEW.json',dict(source_revision=F,deployed_features=features,source_cfg_sites=cfg,native='NIK historical bodies reused only where body hash matches. No new native compile; changed entry dispatch checked from frozen source and new SBF MIR.',sbf='NKX_pool2 exact deployed release MIR includes Solana-only stack gate.',claim='Inventory of cfg and conservative alternatives only; no native semantic association credit.'))
(E/'NKZ_INVENTORY.json.sha256').write_text(sha((E/'NKZ_INVENTORY.json').read_bytes())+'\n')
print('NKZ diff:216 rows removed; guards13->6; held4->3; classes113/124/11/30; estimate124..248 conditional.')
