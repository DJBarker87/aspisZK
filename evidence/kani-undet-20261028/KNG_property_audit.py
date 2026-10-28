from pathlib import Path
import json,re,hashlib
E=Path(__file__).resolve().parent;rows=json.loads((E/'KNG_RUN_PLAN.json').read_text());out=[]
def extract(text,name):
 m=re.search(r'fn\s+'+name+r'\s*(?:<[^\n]*>)?\s*\([^\n]*',text);assert m,name
 start=text.index('{',m.start());depth=1;j=start+1
 while depth:depth+=(text[j]=='{')-(text[j]=='}');j+=1
 return text[start:j]
for r in rows:
 mod=r['positive'].split('::')[-2];name=r['positive'].split('::')[-1]
 text=(E/(mod+'.rs.txt')).read_text()
 if mod=='KNG_LPi_contracts':
  positive=extract(text,'check_q');control=extract(text,'KNG_check_q_negative')
  assert control==positive.replace('assert_eq!(buf[j],(x[k/4]','assert_ne!(buf[j],(x[k/4]',1)
  m=re.search(r'qcase!\('+name+r',([0-9]+),([0-9]+)\);',text);assert m
  instance=dict(width=int(m[1]),offset=int(m[2]))
 else:
  positive=extract(text,name);control=extract(text,name+'_negative');instance=None
  expected=positive.replace('assert!(core::ptr::eq(s.nullifier(),&public.nullifier))','assert!(!core::ptr::eq(s.nullifier(),&public.nullifier))') if r['historical_attempt']=='NBU_K022' else positive.replace('assert_eq!','assert_ne!',1)
  assert control==expected,(r['historical_attempt'],'control mutation differs from packet')
 out.append(dict(historical_attempt=r['historical_attempt'],module=mod,harness=name,instance=instance,positive_body=positive,control_body=control,positive_body_sha256=hashlib.sha256(positive.encode()).hexdigest(),control_body_sha256=hashlib.sha256(control.encode()).hexdigest(),same_domain_and_calls=True,control_change='Recorded pointer-identity assertion inverted in both variants (projection); otherwise first equality/writer payload equality inverted. Other observations unchanged.',function_pointer_dependence=False))
(E/'KNG_PROPERTY_AUDIT.json').write_text(json.dumps(out,indent=2)+'\n');print(len(out),'exact domain-preserving control comparisons passed')
