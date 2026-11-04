"""Mutation checks on the exact admitted NFT recipes; no prover rerun."""
import importlib.util,pathlib,json,copy
E=pathlib.Path(__file__).resolve().parent
sp=importlib.util.spec_from_file_location('NFT_checks',E/'NFT_certify.py');m=importlib.util.module_from_spec(sp);sp.loader.exec_module(m)
out=json.loads(m.lzma.open(E/'NFT_COMPOSED_LEDGER.json.xz').read());rows={r['row']:r for r in out['rows']};certs=m.J('NFT_CERTIFICATES.json');tests=[]
for rid,c in certs.items():
 row=rows[rid];base=m.by[rid]
 assert not m.NFK.row_checks(row,base,c)
 for label,change in [('body',lambda r:r.update(frozen_body_sha256='0'*64)),('claims',lambda r:r.update(selected_claims=[])),('open child',lambda r:r.update(open_transitive_dependencies=['missing'])),('hypothesis',lambda r:r['named_hypotheses'][0].update(discharged_by=None))]:
  bad=copy.deepcopy(row);change(bad);assert m.NFK.row_checks(bad,base,c);tests.append(rid+': '+label)
 for label,change in [('review seal',lambda x:x.update(domain='forged domain')),('inner assumption',lambda x:x.update(inner_hypotheses_remaining=['unproved']))]:
  bad=copy.deepcopy(c);change(bad)
  try:m.NFK.certificate_checks(m.Support(),bad)
  except(ValueError,AssertionError):tests.append(rid+': '+label)
  else:raise AssertionError(label)
(E/'NFT_TESTS.json').write_text(json.dumps(dict(status='PASS',tests=tests),indent=1)+'\n');print('PASS',len(tests),'mutations')
