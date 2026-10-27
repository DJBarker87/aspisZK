from pathlib import Path
import re,json,hashlib
E=Path(__file__).resolve().parent;R=E.parents[1]
source=R/'lean/FJv_Statements.lean';sha=hashlib.sha256(source.read_bytes()).hexdigest()
found=[]
for f in E.glob('FJv_*/receipt.json'):
 x=json.loads(f.read_text())
 if x['exit_status']==0 and x['source_hashes'].get(source.name)==sha:found.append((x['attempt'],f.parent))
assert found, 'Missing exact-current-source kernel print pass'
a,folder=sorted(found)[-1];log=(folder/'stdout.log').read_text()
labels=[('AspisR1.FJu_Top.deployed','FJv_before_top'),('AspisR1.FJv_Top.deployed','FJv_after_top'),('AspisR1.FJv_Specialised.deployed','FJv_before_deployed'),('AspisR1.FJv_Deployed.deployed','FJv_after_deployed')]
parts=[];out=[]
for n,label in labels:
 m=re.search('BEGIN KERNEL TYPE '+re.escape(n)+r'\n(.*?)\nEND KERNEL TYPE '+re.escape(n),log,re.S)
 assert m,n
 t=m.group(1).strip();assert '⋯' not in t and '...' not in t, 'Truncated pretty print'
 assert 'sorryAx' not in t
 dest=E/(label+'.kernel.lean.txt');dest.write_text('-- Complete kernel type of '+n+'\n'+t+'\n')
 out.append(dict(theorem=n,artifact=dest.name,sha256=hashlib.sha256(dest.read_bytes()).hexdigest(),print_receipt=a))
 parts.append('## '+n+'\n\n```lean\n'+t+'\n```\n')
p=E/'FJv_STATEMENTS.md';s=p.read_text().split('<!-- KERNEL STATEMENTS -->')[0]
s=s.replace('The statements will be inserted from the focused Lean kernel type-print receipt,\nwith fully explicit names, universes and deep terms; no proof-body reduction.',f'The statements below come from focused kernel type-print receipt {a},\nwith fully explicit names, universes and deep terms; no proof-body reduction.')
p.write_text(s+'<!-- KERNEL STATEMENTS -->\n\n'+''.join(parts))
(E/'FJv_statement-artifacts.json').write_text(json.dumps(out,indent=2)+'\n')
print('Wrote all four full kernel types from',a)
