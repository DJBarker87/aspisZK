from pathlib import Path
import hashlib,re,json
R=Path(__file__).resolve().parents[2];E=R/'evidence/pv-relink-20261028'
sha=lambda b:hashlib.sha256(b).hexdigest()
def clean(s):return re.sub(r'/\*.*?\*/|//[^\n]*','',s,flags=re.S)
def tokens(s):return re.findall(r'::|=>|[A-Za-z_]\w*|\d+|[^\s]',clean(s))
def body(s,needle):
 s=clean(s);a=s.index(needle);a=s.index('{',a);d=0
 for i in range(a,len(s)):
  if s[i]=='{':d+=1
  if s[i]=='}':
   d-=1
   if d==0:return s[a:i+1]
 raise ValueError(needle)
def checked(s,needle,expected):
 b=body(s,needle);assert tokens(b)==tokens(expected),(needle,b,expected)
 return dict(needle=needle,body=b,token_sha256=sha(' '.join(tokens(b)).encode()),complete_body_tokens_match=True)
def std(f):
 p=E/'stdlib'/f;b=p.read_bytes();prior=json.loads((R/'evidence/pv-cblib-20261027/std-provenance.json').read_text())[f];assert sha(b)==prior['sha256'];return b.decode()
def report(row,checks,differences,laws,nonvacuity):
 d=dict(row=row,evidence_class='structural (K-1 substitute)',checks=checks,differences=differences,complete_Result_laws=laws,nonvacuity=nonvacuity,suspended_Kani='K-1: retained original evidence; NOT a native link',boundary='Candidate value/library primitive interpretation only; original source-image, allocation/world, compiler and deployment residuals retained. No universal machine/compiler refinement is inferred from finite validation.')
 (E/(row+'-binding.json')).write_text(json.dumps(d,indent=2)+'\n');print(row,'complete-body structural checks PASS')
