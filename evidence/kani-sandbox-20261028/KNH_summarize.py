from pathlib import Path
import json,re,hashlib
E=Path(__file__).resolve().parent
rows=[];harnesses=[]
for p in sorted(E.glob('KNH_[NO][0-9][0-9][0-9]/receipt.json')):
 r=json.loads(p.read_text());s=(p.parent/'stdout.log').read_text()
 if r['exit_status'] in [241,143]:kind='INTERRUPTED'
 elif 'panicked at' in s:kind='COMPILER_PANIC'
 elif "doesn't implement `kani::Arbitrary`" in s:kind='MISSING_ARBITRARY'
 elif r['exit_status']==124 or 'timed out' in s.lower():kind='TIMEOUT'
 elif 'VERIFICATION:-' in s:kind='CHECK_FAILURE' if 'VERIFICATION:- FAILED' in s else 'PASS'
 elif 'error:' in s:kind='CLI_OR_COMPILE_ERROR'
 else:kind='UNCLASSIFIED'
 blocks=re.split(r'Checking harness ([^\n]+)\.\.\.\n',s)
 results=[]
 for i in range(1,len(blocks),2):
  name=blocks[i];body=blocks[i+1]
  result='TIMEOUT' if 'timed out' in body.lower() else 'FAIL' if 'VERIFICATION:- FAILED' in body else 'PASS' if 'VERIFICATION:- SUCCESSFUL' in body else 'TIMEOUT' if 'Timed out' in body else 'NO_VERDICT'
  failed=re.findall(r'- Status: FAILURE\s*\n\s*- Description: "([^\n]*)"',body)
  x=dict(attempt=r['attempt'],harness=name,result=result,failed_descriptions=failed);results.append(x);harnesses.append(x)
 rows.append(dict(attempt=r['attempt'],tool_version=r['tool_version'],target=r['target'],classification=kind,exit=r['exit_status'],wall_seconds=r['wall_seconds'],peak_rss_kib=int(r['peak_rss_kib']),swaps=r['swaps'],strict_graph_preflight=(E/(r['attempt']+'-strict-graph.json')).exists(),harness_results=results))
(E/'KNH_RESULTS.json').write_text(json.dumps(rows,indent=2)+'\n')
(E/'KNH_HARNESS_RESULTS.json').write_text(json.dumps(harnesses,indent=2)+'\n')
new=[r for r in rows if r['tool_version']=='new'];old=[r for r in rows if r['tool_version']=='old']
print(json.dumps(dict(new=len(new),old=len(old),new_counts={k:sum(r['classification']==k for r in new) for k in sorted({r['classification'] for r in new})},old_counts={k:sum(r['classification']==k for r in old) for k in sorted({r['classification'] for r in old})}),indent=2))
