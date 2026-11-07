from pathlib import Path
import re,json,hashlib
E=Path(__file__).resolve().parent;manifest=json.loads((E/'NLU_HEAD_INPUT.json').read_text());source=E.parent.parent/manifest['source'];raw=source.read_text();assert hashlib.sha256(source.read_bytes()).hexdigest()==manifest['sha256']
body=raw[raw.index(' match s.next with\n')+len(' match s.next with\n'):raw.index('\nend AspisR1.NLC_Finish')];parts=re.split(r'^ \| (.+?) =>\n?',body,flags=re.M);seen=[]
normalize=lambda x:re.sub(r'\s+','',x)
for labels,code in zip(parts[1::2],parts[2::2]):
 for label in labels.split(' | '):
  n=label.strip().removeprefix('.');seen.append(n);p=E/'NLU_generated'/('NLU_Head_'+n+'.lean');text=p.read_text();a=text.index(' let l:=s.locals\n')+len(' let l:=s.locals\n');b=text.index('\ntheorem source_',a)
  assert normalize(text[a:b])==normalize(code),(n,'source occurrence drift')
  assert '#print axioms source_'+n in text
assert seen==manifest['occurrences'] and len(seen)==34
out=dict(status='PASS',source_sha256=manifest['sha256'],dispatcher_heads=34,major=32,expanded_occurrences=35,whitespace_only_normalization=True)
(E/'NLU_HEAD_CHECK.json').write_text(json.dumps(out,indent=1));print(json.dumps(out))
