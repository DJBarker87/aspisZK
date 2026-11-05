from pathlib import Path
E=Path(__file__).resolve().parent
source=(E/'NGX_stage2_tests.py').read_text().replace("E/'NGX_stage2_validate.py'","E/'NGX_stage3_validate.py'").replace("E/'NGX_TESTS.json'","E/'NGX_STAGE3_TESTS.json'")
source=source.replace("assert v.validate()['status']=='PASS'",'''def missingdomain(raw):
 x=json.loads(raw);next(f for f in x['functions']if f['rows']==['TX1:138'])['domain_roots']=[];return json.dumps(x).encode()
mutation('prefix domain roots retained','NGX_CLOSED.json',missingdomain)
def missingpacking(raw):
 x=json.loads(raw);next(f for f in x['functions']if f['rows']==['TX1:163'])['lean_root']='AspisR1.NGX_SamplerStages.pass_emitted';return json.dumps(x).encode()
mutation('sampler packing association retained','NGX_CLOSED.json',missingpacking)
mutation('reused sampler validation cannot be forged','NGX_NGT_REVALIDATION.json',jset('status','PASS_WITHOUT_CHECKS'))
mutation('native begin control cannot pass','NGX_K030/receipt.json',jset('exit_status',0))
assert v.validate()['status']=='PASS' ''')
exec(compile(source,__file__,'exec'))
