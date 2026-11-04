"""Validate a completed additive stage, report it, and commit only NEY evidence."""
from pathlib import Path
import sys,json,subprocess,datetime
import NEY_validate as v
import NEY_build_certificates as build
E=v.E;R=v.R
stage=sys.argv[1];assert stage in ['terminal','public','final']
from NEY_frozen_identity import check as frozen_identity
for path in sorted(E.glob('NEY_K*/receipt.json')):
 a=path.parent.name
 (E/(a+'-frozen-identity.json')).write_text(json.dumps(frozen_identity(a),indent=1)+'\n')
base=v.baseline();packet=build.build(base);out=v.compose(base,packet)
summary=v.inherited.inherited.summary(out)
(E/('NEY_'+stage.upper()+'_VALIDATION.json')).write_text(json.dumps(summary,indent=1)+'\n')
# Keep every conservative inventory edge, including alternatives and OPENs.
import NEY_bridge_checks as b
by={}
for row in out['rows']:by.setdefault(row['function'],[]).append(row)
edges=[]
for edge in b.SPEC['internal_edges']:
 f,g=edge.split(' -> ');obs=[o for r in by[f] for o in r['caller_domain_obligations'] if o.get('callee')==g]
 closed=bool(obs) and all(o['status']=='CLOSED' and o['discharged_by'] for o in obs)
 edges.append(dict(edge=edge,status='CLOSED' if closed else 'OPEN',certificates=list(dict.fromkeys(o['discharged_by'] for o in obs if o['discharged_by'])),required_named_hypotheses=list(dict.fromkeys(h for o in obs for h in o.get('required_named_hypotheses',[]))),obstacle=None if closed else 'Actual caller-to-callee same inputs, carrier, full Result/state/effects and selected PacketDomain remain unbound; preserve all alternative targets'))
(E/'NEY_EDGES.json').write_text(json.dumps(edges,indent=1)+'\n')
(E/'NEY_CHECKED_ROWS.json').write_text(json.dumps([r for r in out['rows'] if r['function'] in b.SPEC['functions']],indent=1)+'\n')
r=subprocess.run([sys.executable,str(E/'NEY_validator_tests.py')],capture_output=True,text=True);(E/('NEY_'+stage.upper()+'_TESTS.log')).write_text(r.stdout+r.stderr);assert r.returncode==0
(E/'NEY_STAGE_STATUS.json').write_text(json.dumps(dict(stage=stage,utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),closed_rows=summary.get('closed_row_count'),closed_roots=summary.get('root_closed_count'),edge_closed=sum(x['status']=='CLOSED' for x in edges),certificates=list(packet['NEY_certificates']),target='not yet established'),indent=1)+'\n')
files=[str(p.relative_to(R)) for p in E.rglob('*') if p.is_file() and '__pycache__' not in str(p) and p.name not in ['NEY_ACTIVE.json','NEY_LEAN_ACTIVE.json']]
assert all((R/p).stat().st_size<=20_000_000 for p in files)
subprocess.run(['git','add','--',*files],cwd=R,check=True)
subprocess.run(['git','diff','--cached','--check','--','*.py','*.lean','*.md'],cwd=R,check=True)
subprocess.run(['git','commit','--quiet','-m','Validate '+stage+' slice S composition checkpoint'],cwd=R,check=True)
print(json.dumps(json.loads((E/'NEY_STAGE_STATUS.json').read_text())),flush=True)
