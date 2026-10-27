from pathlib import Path
import json,re,hashlib,subprocess
E=Path(__file__).resolve().parent;R=E.parents[1];L=R/'docs/research/v8-r0-zk-20261009/lean'
rs=[json.loads(p.read_text()) for p in sorted(E.glob('J*/receipt.json'))];ks=[json.loads(p.read_text()) for p in sorted(E.glob('K*/receipt.json'))]
final={}
for r in rs:
 if r['exit']==0:final[r['module']]=r
manifest=[];ax=[]
for m,r in final.items():
 p=L/(m+'.lean');sha=hashlib.sha256(p.read_bytes()).hexdigest();assert sha==r['source_sha256'],m
 s=p.read_text();assert not re.search(r'\b(?:sorry|admit|native_decide|implemented_by)\b|^axiom\s|set_option max(?:Heartbeats|RecDepth)',s,re.M),m
 for line in r['axioms']:
  assert 'sorryAx' not in line
  a=re.search(r'axioms: \[(.*?)\]',line)
  if a:assert set(a[1].split(', ')) <= {'propext','Classical.choice','Quot.sound'},line
  ax.append(line)
 declarations=re.findall(r'^theorem (\w+)',s,re.M)
 prints=re.findall(r'^#print axioms ',s,re.M)
 assert len(prints)==len(r['axioms']),(m,len(prints),len(r['axioms']))
 manifest.append(dict(module=m,path=str(p.relative_to(R)),sha256=sha,accepted_attempt=r['attempt'],declarations=declarations))
summary=dict(lean_charged=len(rs),lean_pass=sum(r['exit']==0 for r in rs),lean_fail=sum(r['exit']!=0 for r in rs),kani_charged=len(ks),kani_pass=sum(r['exit']==0 for r in ks),accepted_modules=len(final),printed_declarations=len(ax),peak_lean_rss_kib=max(int(r['peak_rss_kib'] or 0) for r in rs),swaps=sum(int(r['swaps'] or 0) for r in rs+ks),V380='OPEN',endpoint_premises_removed=0,trust_fields_added=0)
(E/'SUMMARY.json').write_text(json.dumps(summary,indent=2)+'\n');(E/'AUDIT-MANIFEST.json').write_text(json.dumps(manifest,indent=2)+'\n');(E/'AXIOMS.md').write_text('# Accepted axiom lines\n\nOnly final successful sources are accepted. Failed elaborations are excluded.\n\n```text\n'+'\n'.join(ax)+'\n```\n')
index='| Attempt | Target | Exit | Wall | Peak RSS KiB | Swap | Revision |\n|---|---|---:|---|---:|---:|---|\n'
for r in rs:
 index+=f"| [J{r['attempt']}](J{r['attempt']}/receipt.json) | {r['module']} | {r['exit']} | {r['wall']} | {r['peak_rss_kib']} | {r['swaps']} | {r['source_revision'][:10]} |\n"
for i,r in enumerate(ks,1):index+=f"| [K{i:02}](K{i:02}/receipt.json) | {r['target']} | {r['exit']} | {r['wall']} | {r['peak_rss_kib']} | {r['swaps']} | {r['source_revision'][:10]} |\n"
(E/'INDEX.md').write_text(index);base=(E/'base.txt').read_text().strip();(E/'HISTORY.txt').write_bytes(subprocess.check_output(['git','log','--oneline',base+'..HEAD'],cwd=R));print(json.dumps(summary,indent=2))
