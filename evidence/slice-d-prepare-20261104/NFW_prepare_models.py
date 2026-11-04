from pathlib import Path
import re,json,hashlib
E=Path(__file__).resolve().parent;R=E.parents[1];records=[]
(E/'NFW_Bind.lean').write_text('''import NFQ_STAGE2_IMPORT
set_option autoImplicit false
namespace AspisR1.NFW_Bind
open Aeneas Aeneas.Std Result
theorem same {α β : Type} (m : Result α) (f g : α→Result β)
 (h : ∀ x,f x=g x) : (m >>= f)=(m >>= g) :=
 congrArg (fun k=>m >>= k) (funext h)
#print axioms same
end AspisR1.NFW_Bind
''')
for old,new in [('NBA_Transcript','NFW_Transcript'),('NBL_PrepareControl','NFW_PreparedControl'),('NBL_PrepareResults','NFW_PreparedResults'),('NBR_PreparedFields','NFW_PreparedFields')]:
 source=(R/'lean'/(old+'.lean')).read_text();body=[]
 for line in source.splitlines():
  if not line.startswith('import '):body.append(line)
 text='\n'.join(body)+'\n'
 text=text.replace('NBA_QueryJoin.bind_same','NFW_Bind.same')
 for a,b in [('NBL_PrepareControl','NFW_PreparedControl'),('NBL_PrepareResults','NFW_PreparedResults'),('NBR_PreparedFields','NFW_PreparedFields'),('NBA_Transcript','NFW_Transcript')]:text=re.sub(r'\b'+a+r'\b',b,text)
 imports=['NFQ_STAGE2_IMPORT','NFW_Bind']
 if new in ['NFW_PreparedResults','NFW_PreparedFields']:imports+=['NFW_PreparedControl']
 if new=='NFW_PreparedFields':imports+=['NFW_PreparedResults']
 text=''.join('import '+n+'\n' for n in imports)+text
 (E/(new+'.lean')).write_text(text)
 records.append(dict(source='lean/'+old+'.lean',source_sha256=hashlib.sha256(source.encode()).hexdigest(),target=new+'.lean',target_sha256=hashlib.sha256(text.encode()).hexdigest(),changes='imports, proof namespace and existing bind-congruence helper owner only'))
(E/'NFW_PREPARED_MODEL_PROVENANCE.json').write_text(json.dumps(records,indent=1)+'\n')
