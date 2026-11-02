import subprocess,json
from NEM_install import install
from NEM_artifacts import E,R,ref,theorem,native_support
from NEM_kind_checks import FUNCTIONS,PAIRS
b=json.loads((R/'evidence/native-ledger3-20261029/NDT_LEDGER.json').read_text())
for case,f in FUNCTIONS.items():
 rs=[r for r in b['rows'] if r['function']==f];data=subprocess.check_output(['git','show',b['frozen_revision']+':'+f.split('::')[0]],cwd=R)
 ts=[theorem('NEM_KindInstance',{'statement':'statement_window','payment':'payment_window','parse':'parser_result_frame'}[case])];aa=list(dict.fromkeys(a for p in PAIRS[case] for a in p))
 q=dict(function=f,case=case,all_typed_inputs=True,no_acceptance_precondition=True,method='actual getter/parser on same caller variant or byte, complete scalar frame, accepted enclosing-model association',trust_classification='P6/D188 option A reclassification',inner_hypotheses_remaining=[],native_pairs=PAIRS[case],native_support=native_support(aa),frozen_bodies=[data[r['frozen_body_byte_range'][0]:r['frozen_body_byte_range'][1]].decode() for r in rs],theorems=ts)
 install(f,'kind_composition',q,ts,native_support(aa),ts,ts,'Actual frozen typed enum getter or u8 parser invoked on caller SAME variant or header byte5; no acceptance premise. Every field is arbitrary. Native scalar write frame covers every observed cell of arbitrary prestate; parser includes all invalid bytes and complete Result. NEM_KindInstance associates the SAME variant to the actual adopted enclosing encoder tag via accepted NBN_U05.encoder_kind, and the parser via NBD_TerminalProjection.source_kind. Payment joins the SAME public variant to arbitrary common carrier; no invented separate emitted getter. Native semantics is P6/D188 option A reclassification.')
