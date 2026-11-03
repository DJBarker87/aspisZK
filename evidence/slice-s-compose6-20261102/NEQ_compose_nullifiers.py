from pathlib import Path
import subprocess,hashlib
from NEQ_install import install
from NEQ_artifacts import ref,theorem,native_support
from NEQ_nullifier_checks import FUNCTIONS,THEOREMS
E=Path(__file__).resolve().parent;R=E.parent.parent
ts=[theorem(*n.rsplit('.',1)) for n in THEOREMS]
for case,f in FUNCTIONS.items():
 pair=['NEQ_K083','NEQ_K084'] if case=='statement' else ['NEQ_K085','NEQ_K086'];native=native_support(pair)
 source=subprocess.check_output(['git','show','4bb3b3f51e16b4525f1d10336e2b0bcbbd775387:'+f.split('::')[0]],cwd=R,text=True);impl=f.split('::')[1];a=source.index('impl '+impl+' {');a=source.index('    pub fn nullifier(',a);z=source.index('\n    }',a)+6;body=source[a:z]
 q=dict(function=f,case=case,pairs=[pair],method='ruling y prime exact borrowed-place identity and same-variant extracted projection',domain='every typed variant and raw Digest; no validation or canonicality assumption',inner_hypotheses_remaining=[],trust_classification='P6/D188 option A reclassification',native_support=native,theorems=ts,manifests=[ref(E/(a+'-nullifier.json')) for a in pair],frozen_body=body,frozen_body_sha256=hashlib.sha256(body.encode()).hexdigest(),empty_external_modifies=True,ordered_effects=[],same_borrowed_place=True)
 install(f,'nullifier_getter',q,ts,native,ts,ts,'The exact frozen borrowed getter is a two-variant public.nullifier field projection. The actual native getter returns precisely the same field address/lifetime under each typed variant; a wrong anchor-root place fails with the same harness name. Its immutable borrow neither writes external state nor emits events. The adopted tuple projection equals the identical public.nullifier on every raw carrier; joining a common record changes no payment nullifier. No canonicality or successful-child premise remains. Ruling y prime and P6/D188 option A are trust reclassification, not removal.')
