from pathlib import Path
import subprocess,json,hashlib
from NEQ_install import install
from NEQ_artifacts import ref,theorem,native_support
from NEQ_result_validator_checks import F,THEOREMS
E=Path(__file__).resolve().parent;R=E.parent.parent
source=subprocess.check_output(['git','show','4bb3b3f51e16b4525f1d10336e2b0bcbbd775387:'+F.split('::')[0]],cwd=R,text=True);a=source.index('fn validate_result(');z=source.index('\n}',a)+2;body=source[a:z]
ts=[theorem(*n.rsplit('.',1)) for n in THEOREMS];native=native_support([f'NEQ_K{n:03}' for n in range(44,48)])
q=dict(function=F,method='ruling y exact frozen caller with local full-Result oracles and concrete substitution',domain='every typed Result record; no canonicality or successful child assumption',inner_hypotheses_remaining=[],trust_classification='P6/D188 option A reclassification',pairs=[['NEQ_K044','NEQ_K045'],['NEQ_K044','NEQ_K046'],['NEQ_K044','NEQ_K047']],native_support=native,theorems=ts,manifests=[ref(E/f'NEQ_K{n:03}-result-validator.json') for n in range(44,48)],frozen_body=body,frozen_body_sha256=hashlib.sha256(body.encode()).hexdigest(),full_Result=True,ordered_effects=True,empty_external_modifies=True)
install(F,'result_validator',q,ts,native,ts[3:5],ts,'The frozen validate_result body erases exactly from the native instrumented source. Full arbitrary lane and afterstate Results retain every error, source rejection priority and actual child places. The complete afterstate reply is discarded as in source. Both child native bridges are already CLOSED and all typed result records establish their domains; no canonicality/success assumption is added. Local log records exact reached-child prefix, while safe immutable inputs and pure children preserve external state. Lean result_state_effects substitutes the same argument-bearing source trace into the adopted validator model. P6/D188 option A is trust reclassification, not removal.')
