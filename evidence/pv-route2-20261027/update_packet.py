from pathlib import Path
import json,re,hashlib
D=Path('evidence/pv-route2-20261027');rows=json.loads((D/'candidates.json').read_text())
rowids={36:'V187',79:'V201',132:'V228',133:'V229',205:'V231',212:'V234',215:'V235',216:'V236',217:'V237',219:'V238',222:'V239',223:'V240',224:'V241',226:'V243',227:'V244',228:'V245',230:'V247',249:'V256',250:'V257',251:'V258',252:'V259',253:'V260',254:'V261',258:'V264'}
selected={121:'aeneas-121-04',222:'aeneas-222-03',253:'aeneas-253-03',79:'aeneas-79-03-local'}
allops=sorted(set(rowids)|{117,121,134});table=[];counts={'accepted_emission':0,'refused':0,'unmeasured':0};detail=[]
for op in allops:
 r=next((r for r in rows if r['op']==op),None);row=rowids.get(op,'op'+str(op));name=selected.get(op,f'aeneas-{op}-01');p=D/name/'receipt.json'
 if not r:status='UNMEASURED: no variant completed';counts['unmeasured']+=1;kind='prover-local required';lines='—';callers='not prepared';impact='unresolved';law='not established'
 else:
  kind=r['kind'];lines=f"+{r['added']}/−{r['removed']}";callers=str(len(r['callers']))+' chain entries';impact='host-only' if kind=='prover-local' else 'cost-probe only';law='source/Result transport still required'
  if p.exists():
   receipt=json.loads(p.read_text());log=(p.parent/'output.log').read_text();error=re.search(r'fail-closed preflight: ([^"\n]+)',log)
   if receipt['exit']==0:
    status='ACCEPTED emission';counts['accepted_emission']+=1
   else:
    counts['refused']+=1
    status='REFUSED: '+(error[1] if error else ('InterpBorrows.ml:2731' if 'InterpBorrows.ml' in log else ('Not_found; InterpReduceCollapse.ml:1991' if 'InterpReduceCollapse.ml' in log else 'see log')))
  else:status='PENDING actual extractor measurement';counts['unmeasured']+=1
  if op==79:status+=' (measured shared-array version; owned-array successor pending)'
 table.append(f'|{op} / {row}|{kind}|{lines}|{callers}|{status}|{law}|')
 detail.append(dict(op=op,row=row,variant=kind,patch=str(D/'patches'/f'{op}.patch') if r else None,lines=lines,caller_chain=r['callers'] if r else [],status=status,receipt=str(p) if p.exists() else None,impact=impact,law=law))
(D/'ROWS.json').write_text(json.dumps(dict(counts=counts,rows=detail),indent=2)+'\n')
text='\n## Per-op table\n\n'+f"Counts on completed measurements: {counts['accepted_emission']} accepted emissions, {counts['refused']} refusals, {counts['unmeasured']} unmeasured rows. Empty emissions and resource holds are excluded. No callback row is discharged.\n\n"
text+='Caller-chain entries count required/copied chain descriptions, **not** completed caller edits. The detailed chain is in `candidates.json`; only79/223/230 have host redirects. For refused shared-source deltas the actual caller-edit count is0. In-place body changes have0 caller edits. Four successful small patches total46 added/10 removed lines.\n\n'
text+='|op / row|Required form|Patch lines|Caller chain|Pinned extraction|Existing law applicability|\n|---|---|---|---|---|---|\n'+'\n'.join(table)+'\n'
text+='\nFull exact errors, target commands, source revisions and resource receipts are in each linked receipt directory under the evidence packet. Op79/253 internal exceptions occur after preflight; they must not be called reference-guard refusals. No source counterexample is claimed.\n'
p=Path('design/PV-ROUTE2-20261027.md');s=p.read_text();marker='\n## Per-op table\n';s=s.split(marker)[0]+text;p.write_text(s)
# Current source hashes bind evidence files independently of mutable host snapshots.
files={str(p):dict(size=p.stat().st_size,sha256=hashlib.sha256(p.read_bytes()).hexdigest()) for folder in ['patches','probes','source-inputs','generated','lean','lean-direct'] for p in (D/folder).rglob('*') if p.is_file()}
(D/'source-manifest.json').write_text(json.dumps(files,indent=2)+'\n')
print(counts)
