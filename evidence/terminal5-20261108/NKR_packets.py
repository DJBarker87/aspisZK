from pathlib import Path
import json,lzma,hashlib
E=Path(__file__).resolve().parent;sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
bp=E.parent/'ledger19-20261108/NKN_LEDGER.json.xz';base=json.loads(lzma.decompress(bp.read_bytes()));byid={r['row']:r for r in base['rows']};passed={}
for r in map(json.loads,(E/'NKR_ATTEMPTS.jsonl').read_text().splitlines()):
 p=E/(r.get('module','')+'.lean')
 if r.get('kind')=='lean'and r['exit_status']==0 and p.exists()and r['source_hashes'].get(p.name)==sha(p):passed[p.stem]=r
pairs={(p['positive'],p['negative'])for p in json.loads((E/'NKR_NATIVE_PAIRS.json').read_text())['pairs']}
pair=lambda i:[f'NKR_K{i:03d}',f'NKR_K{i+1:03d}']
specs=[
(225,'NKR_SumCarrier','Canonical SAME left/right4;1<=count<=4;allhelper budgets/n+remaining derived',[['NKR_K011','NKR_K004']],[],[40,41,43]),
(232,'NKR_ScheduleRoot','Canonical SAME packed24,opened.z16,high64,low16;public arbitrary',[pair(i)for i in[12,14,16,7,36]],[260],[230]),
(251,'NKR_DigestComposed','SAMEpublic Domain canonicaldigest/frontierfields,opened.z16,high64,low16;carry/min domains internallyderived',[pair(i)for i in[58,60,62,64,66]],[235],[242,245,246]),
(250,'NKR_DigestComposed','SAME251args/2reply;complete25familyargumentprojection+rawcarrierext',[pair(68)],[251],[]),
(220,'NKR_SumFinishComposed','Canonical SAME scratch103/high64/low16/patterns14;9batch+43pattern domains internallyderived;full4+4',[pair(i)for i in[70,72,74,76,78,42]],[225],[217,219]),
(218,'NKR_SumCopyFull','Canonical actualroot inputs plus reviewedlookup/constantmetadata primitivecuts;full136loop/8rows/residual/active Result',[pair(i)for i in[80,82,84,86,46]],[220],[208,214,215,217,223])]
functions=[];missing=[]
for n,owner,domain,ps,candidates,children in specs:
 row=f'TX1:{n:03d}'
 if owner not in passed or not all(tuple(p)in pairs for p in ps):missing.append(row);continue
 r=byid[row];assert r['status']=='OPEN';roots=['AspisR1.'+owner+'.source']
 if n==218:roots=['AspisR1.NKR_SumCopyRoot.source']
 if n==232:roots.append('AspisR1.NKR_ScheduleAssociation.source')
 functions.append(dict(rows=[row],function=r['function'],frozen_body_sha256=r['frozen_body_sha256'],route='(y)/(ai)(5)/(ad)/(aq)/(aq)(5)/(au) direct P6 hybrid',root_domain=domain,native_pairs=ps,lean_roots=roots,owner_module=owner,root_attempt=passed[owner]['attempt'],source_sha256=sha(E/(owner+'.lean')),complete_carrier=True,premise_policy='Actual typed inputs/canonicality and reviewed primitive native cuts only; SAME child Results/domains/frame derived internally; no Run/Ops/success/desired-output root premise',trust='P6/D188 optionA semantictransport RECLASSIFICATION; inherited ABI/std/allocator/compiler/source-to-ELF retained; none added or removed',status='CANDIDATE',local_gate='PENDING_COMBINED_GATE',credit_waits_next_ledger_gate=True,closed_children=[f'TX1:{i:03d}'for i in children],candidate_child_dependencies=[f'TX1:{i:03d}'for i in candidates],conditional_children_note='NKI234/235/260/233 and own candidates await next ledger; NJX242/245/246 CLOSED in ledger19 and consumed at SAME arguments'))
(E/'NKR_CLOSED.json').write_text(json.dumps(dict(frozen_revision=base['frozen_revision'],headline='AspisR1.RPx_Deployed.deployed',functions=functions,target_established=False,authoritative_delta=0),indent=1))
(E/'NKR_LEDGER_DELTA.json').write_text(json.dumps(dict(baseline=str(bp),baseline_sha256=sha(bp),baseline_counts=base['counts'],authoritative_delta=0,proposed_rows=[f['rows'][0]for f in functions],local_gate='PENDING_COMBINED_GATE',missing_focused_roots=missing,credit_waits_next_ledger_gate=True),indent=1))
print('Reviewable row packets: '+','.join(f['rows'][0]for f in functions))
