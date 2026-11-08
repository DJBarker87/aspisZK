"""Sequential native closure and raw-ax2 checks inside ONE capped scope."""
from pathlib import Path
import json,subprocess,time,re,hashlib,sys
B=Path.cwd();allowed={'propext','Classical.choice','Quot.sound'};stages=[]
expected=json.loads((B/'NNP_RAW_BINARY_EXPECTED.json').read_text())
assert hashlib.sha256((B/'NNP_ProofDriver').read_bytes()).hexdigest()==expected['sha256']
scanpin=json.loads((B/'NNP_SCAN_BINARY_PIN.json').read_text())
assert hashlib.sha256((B/'NNP_native/NNP_ScanNative').read_bytes()).hexdigest()==scanpin['sha256']
for name,command in [('scan',['NNP_native/NNP_ScanNative']),('proof0',['./NNP_ProofDriver','proof0']),('proof1',['./NNP_ProofDriver','proof1'])]:
 start=time.monotonic()
 with (B/('NNP_FINAL_'+name+'.stdout')).open('w') as out:
  r=subprocess.run(['/usr/bin/time','-v','-o','NNP_FINAL_'+name+'.time',*command],stdout=out,stderr=subprocess.STDOUT)
 raw=(B/('NNP_FINAL_'+name+'.stdout')).read_text();tim=(B/('NNP_FINAL_'+name+'.time')).read_text()
 def metric(key):return next((line.split(':',1)[1].strip() for line in tim.splitlines() if key in line),None)
 rows=[json.loads(line.split('NEP_RESULT ',1)[1]) for line in raw.splitlines() if 'NEP_RESULT ' in line]
 ax=re.findall(r"'[^']+' (?:depends on axioms:\s*\[[^\]]*\]|does not depend on any axioms)",raw)
 row=dict(target=name,command=command,exit_status=r.returncode,wall_seconds=time.monotonic()-start,peak_rss_kib=metric('Maximum resident set size'),swaps=metric('Swaps'),raw_results=rows,print_axioms=ax)
 (B/('NNP_FINAL_'+name+'.json')).write_text(json.dumps(row,indent=2)+'\n');stages.append(row);print(json.dumps(row),flush=True)
 assert r.returncode==0,raw[-3000:]
 assert not re.search(r'error:|NEP_FAILURE',raw)
 if name=='scan':
  loaded=[json.loads(l) for l in (B/'NNP_LOADED_scan.jsonl').read_text().splitlines()]
  assert loaded and all(not x['dangling'] and not x['duplicate_owners'] for x in loaded)
  print(json.dumps(dict(modules=len(loaded),declarations=sum(x['declarations'] for x in loaded),dangling=0,duplicate_owners=0)),flush=True)
 else:
  wanted=json.loads((B/'LIBB_AUDIT_ROOTS.json').read_text())['groups'][int(name[-1])]
  assert len(rows)==len(wanted) and {x['root'] for x in rows}==set(wanted)
  assert len(ax)==len(wanted),(len(ax),len(wanted))
  for x in rows:
   assert set(x['walked_axioms'])<=allowed and set(x['collect_axioms'])<=allowed,x
   assert set(x['walked_axioms'])==set(x['collect_axioms']),x
print('NNP_FINAL_ALL_CHECKS_PASSED',flush=True)
