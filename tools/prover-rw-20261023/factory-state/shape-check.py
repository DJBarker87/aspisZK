"""Read-only fail-closed compatibility check. Does not execute candidate014."""
from pathlib import Path
import hashlib,json,sys
E=Path(sys.argv[1]);sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
j=json.loads((E/'emission-audit.json').read_text())
source=E/'backend014/PrePasses.ml.txt'
receipt=json.loads((E/'backend014/receipt.json').read_text())
assert sha(source)==receipt['candidate_source_sha256']['src/PrePasses.ml']
s=source.read_text();lower=s[s.index('let lower_precise_local_drops'):s.index('let retain_called_drop_glue')]
assert '| Drop (({kind = PlaceLocal original; _} as place),' in lower
assert '({kind = FunId (FRegular _); _} as func), Precise, unwind)' in lower
assert '| Drop _ -> [%craise] st.span "ProverRwNativeDrop008: unsupported Drop shape"' in lower
assert '("lower_precise_local_drops", lower_precise_local_drops)' in s
unsupported=[]
for f in j['functions']:
    for d in f['drops']:
        # The exact supported syntactic branch in the pinned candidate014.
        k=d['fn_ptr']['kind']
        supported=('Local' in d['place']['kind'] and 'Fun' in k and
                   'Regular' in k['Fun'] and d['kind']=='Precise')
        if not supported:
            unsupported.append(dict(function_id=f['id'],function_name=f['name'],drop=d))
assert any(r['function_id']==15 and r['drop']['statement_id']==796 and
           'Projection' in r['drop']['place']['kind'] and 'Trait' in r['drop']['fn_ptr']['kind']
           for r in unsupported)
resume=j['selected_resume']
assert resume['def_id']==0 and resume['body']!='Opaque'
assert any(d['fn_ptr']['kind']=={'Fun':{'Regular':15}} and not d['in_unwind']
           for f in j['functions'] if f['id']==0 for d in f['drops'])
out=dict(schema='ProverRwFactoryState-static014-shape-v1',
    source_revision=sys.argv[2],command=sys.argv,
    input_sha256={str(p):sha(p) for p in [E/'emission-audit.json',source,E/'backend014/receipt.json',Path(__file__)]},
    binary_reused=receipt['versioned_binary'],unsupported_drops=unsupported,
    actual_backend_invocations=0,actual_compiler_invocations=0,
    claim='Exact extracted resume calls real Zeroizing glue15; its normal projected trait Drop796 fails the only supported pinned014 Drop pattern. Static rejection-shape evidence, NOT a new Aeneas execution or source/effect proof.',
    print_axioms='N/A: read-only source/shape audit')
(E/'shape-check.json').write_text(json.dumps(out,separators=(',',':'))+'\n')
print('PASS fail-closed shape assessment:',len(unsupported),'unsupported precise Drop sites; no backend launched')
