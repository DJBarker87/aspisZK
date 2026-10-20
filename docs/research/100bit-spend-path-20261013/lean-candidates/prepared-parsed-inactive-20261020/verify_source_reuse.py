from pathlib import Path
import hashlib,json,subprocess
D=Path(__file__).resolve().parent
R=next(x for x in D.parents if (x/'.git').exists())
sha=lambda b:hashlib.sha256(b).hexdigest()
def body(s,sig):
 a=s.index(sig);i=s.index('{',a)+1;depth=1
 while depth:
  if s[i]=='{':depth+=1
  if s[i]=='}':depth-=1
  i+=1
 return s[a:i]
for row in json.loads((D/'parser-source-reuse.json').read_text())['declarations']:
 ref=R/row['reference'];assert sha(ref.read_bytes())==row['reference_file_sha256']
 expected=body(ref.read_text(),row['signature']);assert sha(expected.encode())==row['body_sha256']
 for target in row['targets']:
  text=subprocess.check_output(['git','show',target['revision']+':'+target['path']],cwd=R,text=True)
  actual=body(text,row['signature']);assert actual==expected and sha(actual.encode())==target['body_sha256']
print('PASS: both retained parser methods byte-identical at frozen and parked candidate revisions; no extraction replay')
