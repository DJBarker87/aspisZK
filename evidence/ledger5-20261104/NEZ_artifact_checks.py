"""Focused reporting-only correction and final data integrity checks.

No unchanged slice replay: prove all status/certificate gate code is identical
to the successful NEZ_FINAL revision after removing only markdown().
"""
import ast,collections,copy,json,lzma
import NEZ_validate as v
receipt=v.read(v.E/'NEZ_FINAL.json')
path=str((v.E/'NEZ_validate.py').relative_to(v.R))
previous=v.nen.ndt.git('show',receipt['source_revision']+':'+path)
assert v.sha(previous)==receipt['source_sha256'][path]
def gates(raw):
    tree=ast.parse(raw)
    tree.body=[n for n in tree.body if not isinstance(n,ast.FunctionDef) or n.name!='markdown']
    return ast.dump(tree,include_attributes=False)
assert gates(previous)==gates((v.E/'NEZ_validate.py').read_bytes()),'non-reporting gate changed since final replay'
v.check_inputs()
d=v.read(v.E/'NEZ_LEDGER.json')
raw=v.encode(d).encode()
assert v.sha(raw)==(v.E/'NEZ_LEDGER.json.sha256').read_text().strip()
assert lzma.decompress((v.E/'NEZ_LEDGER.json.xz').read_bytes())==raw
assert v.nen.coverage(d['rows'])==d['coverage']
reported=set().union(*map(set,d['NEZ_slice_validator_results'].values()))
closed={r['row'] for r in d['rows'] if r['composed_status']=='CLOSED'}
rejected={r['row'] for r in d['NEZ_rejected_slice_closures']}
assert reported-closed==rejected
assert all(r['reported_by'] and r['reasons'] for r in d['NEZ_rejected_slice_closures'])
credits={c['receipt']:c for c in d['NEZ_credits']}
for row in d['rows']:
    if row['composed_status']=='CLOSED':
        assert not v.nen.support_gate(row['active_support_receipts'],credits)
        assert all(h['discharged_by'] for h in row['named_hypotheses'])
        assert all(o['status']=='CLOSED' and o['discharged_by'] for o in row['caller_domain_obligations'])
        assert not row['open_transitive_dependencies']
actual_ab={r['row'] for r in d['rows'] if r['composed_status']=='CLOSED' and 'RuntimeReturnData' in r['NEZ_trust_rows']}
assert actual_ab==set(d['NEZ_ab_uses']['closed_native_rows'])
assert len(d['NEZ_ab_uses']['model_support'])==d['NEZ_ab_uses']['model_theorem_count']
alternate=copy.deepcopy(d)
alternate['NEZ_slice_validator_results']=dict(reversed(list(d['NEZ_slice_validator_results'].items())))
assert v.markdown(alternate)==v.markdown(d),'report depends on dictionary insertion order'
md=v.markdown(d).encode();(v.E/'NEZ_LEDGER.md').write_bytes(md)
assert (v.E/'NEZ_LEDGER.md').read_bytes()==md
for p in v.E.rglob('*'):
    if p.is_file():assert p.stat().st_size<=20_000_000,'oversize committed artifact: '+str(p)
outputs={p.name:dict(sha256=v.sha(p.read_bytes()),bytes=p.stat().st_size) for p in [v.E/'NEZ_LEDGER.json.xz',v.E/'NEZ_LEDGER.json.sha256',v.E/'NEZ_LEDGER.md']}
outputs['uncompressed_ledger']=dict(sha256=v.sha(raw),bytes=len(raw))
(v.E/'NEZ_OUTPUTS.json').write_text(json.dumps(outputs,sort_keys=True,indent=2)+'\n')
print(json.dumps(dict(status='PASS',status_gate_AST_identical_to=receipt['source_revision'],reported_rows=len(reported),closed_rows=len(closed),rejected_rows=len(rejected),outputs=outputs),indent=2))
