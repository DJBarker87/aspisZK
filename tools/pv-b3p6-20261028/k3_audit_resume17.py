"""Audit historical selected Kani harnesses at receipt-pinned source hashes."""
from pathlib import Path
import hashlib,json,subprocess,re,lzma
D=Path('evidence/pv-b3p6-20261028');R=D/'resume17';base=Path('tools/pv-b3p6-20261028')
sha=lambda b:hashlib.sha256(b).hexdigest()
cache={}
def pinned(path,h):
 key=(path,h)
 if key in cache:return cache[key]
 p=Path(path)
 if p.exists() and sha(p.read_bytes())==h:result=(p.read_text(),'current tracked source')
 else:
  result=None
  revs=subprocess.check_output(['git','log','--format=%H','--',path],text=True).splitlines()
  for rev in revs:
   b=subprocess.check_output(['git','show',rev+':'+path])
   if sha(b)==h:result=(b.decode(),rev);break
  assert result,key
 cache[key]=result;return result
selected=[]
for p in sorted((D/'resume16/receipts').glob('*-inputs.json')):
 d=json.loads(p.read_text());h=d['harness'];rec=p.parent/d['run']/'receipt/receipt.json'
 if not rec.exists() or json.loads(rec.read_text())['exit_status']!=0:continue
 if not any(x in h for x in ['selector_mask_host_','selector_mask_statement_','reconstruct_10','validate_transition','external_local_packed_raw','internal_linear_lazy']):continue
 snapshots={q:pinned(q,s) for q,s in d['source_hashes'].items()}
 hp=str(base/'v244'/('remaining_equivalence16.rs' if h.startswith('remaining_') else 'equivalence16.rs'))
 src,revision=snapshots[hp];fn=h.split('::')[-1]
 m=re.search(r'((?:#\[.*?\]\s*)+)fn '+re.escape(fn)+r'\s*\([^\n]*',src)
 assert m,h
 body=m.group();assert not re.search(r'static\s+mut|thread_local!|Atomic\w*|(?:Ref|Unsafe)?Cell|Mutex|Once(?:Cell|Lock)',body),h
 assert 'shared_callee16' not in body,h
 kmx=(base/'kmx/KMX_stubs.rs').read_text();assert sha(kmx.encode())==d['KMX_stubs_sha256']
 assert not re.search(r'static\s+mut|thread_local!|Atomic\w*|(?:Ref|Unsafe)?Cell|Mutex|Once(?:Cell|Lock)',kmx)
 group=('host-mask' if 'selector_mask_host_'in h else 'statement-mask' if 'selector_mask_statement_'in h else 'reconstruct' if 'reconstruct'in h else 'transition' if 'validate'in h else 'external' if 'external_'in h else 'internal')
 index=json.loads((R/'host-recovery'/('std-'+group)/'index.json').read_text())
 matches=[r for r in index['records'] if r['harness']['pretty_name']==h];assert matches,h
 syms=[]
 for r in matches:
  f=R/'host-recovery'/('std-'+group)/Path(r['symbol_dump']).name
  b=f.read_bytes();assert sha(b)==r['symbol_dump_sha256']
  t=next(x['symbolTable']for x in json.loads(lzma.decompress(b))if 'symbolTable'in x)
  assert not any('shared_callee16'in k for k in t),h
  for k,v in t.items():
   if v.get('type',{}).get('id')=='code':
    syms.append(v.get('prettyName',k))
  assert not any(re.search(r'::(?:USED|TAG|LEFT|RIGHT|OUTPUT)(?:::|$)',k)for k in t)
 selected.append(dict(run=d['run'],harness=h,receipt=str(rec),source_sha256=d['source_hashes'][hp],source_revision=revision,source_excerpt=body,KMX_sha256=d['KMX_stubs_sha256'],symbol_dumps=[r['symbol_dump_sha256'] for r in matches],reachable_code_symbols=len(set(syms)),writable_statics_in_harness_stubs_or_oracles=False,shared_static_oracle_reached=False,k3_status='NOT EXPOSED by source and exact selected symbol listing',std_parity=json.loads((R/'STD-PARITY.json').read_text())['groups'][group]['parity_pass']))
out=dict(method='Receipt-pinned historical source snapshots; actual selected harness and KMX stub inspection; exact recorded symbol dumps exclude shared static oracle. Unused crate module shared_callee16 is not reached by these harnesses.',selected=selected,suspended=[dict(harness='equivalence16::shared_repeat16',reason='writes shared_callee16 mutable static memo table; SUSPENDED (K-3)'),dict(harness='equivalence17::sum_high_nodes',run='K73931',reason='shared static oracle stubs selected; SUSPENDED (K-3); no matched control'),dict(harness='equivalence17::sum_high_path',run='K73932',reason='shared static oracle stubs selected; SUSPENDED (K-3); no matched control')],new_runs='Every new run requires a matched failing control and no writable static. Historical timeouts are not positive credit.',limitations='This is the requested manual/script K-3 check, not a substitute for the lead EXPOSED/NOT-EXPOSED classifier when it arrives. Parity failures remain withheld.')
(R/'K3-AUDIT-D537.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(dict(selected=len(selected),suspended=out['suspended'])))
