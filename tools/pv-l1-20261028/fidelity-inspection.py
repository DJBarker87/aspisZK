"""Per-function ruling-n inspection. This records model scope, not native credit."""
from pathlib import Path
import json,re,hashlib,subprocess
R=Path(__file__).resolve().parents[2];E=R/'evidence/pv-l1-20261028';rows=json.loads((E/'source-frontier.json').read_text());s=json.loads((E/'focused-project-sources.json').read_text())['R1Z.ProverRwFullFuns'];out=[]
for r in rows:
 n=r['source_function'];a=s.index('def '+n+'\n') if 'def '+n+'\n' in s else s.index('def '+n+' ');end=s.find('\n/--',a);raw=s[a:end if end>=0 else len(s)]
 prefix,name=n.split('.',1);name=name.split('_loop')[0].split('.')[0] if '_loop' in name else name.split('.')[-1]
 p=R/'crates/aspis-r1-cost-probe/src'/(prefix+'.rs');rust=p.read_text();matches=list(re.finditer(r'\bfn\s+'+re.escape(name)+r'\s*(?:<|\()',rust))
 back=sorted(set(re.findall(r'\b[A-Za-z_][A-Za-z_0-9]*back[A-Za-z_0-9]*\b',raw)))
 out.append(dict(module=r['module'],source_function=n,emission_sha256=hashlib.sha256(raw.encode()).hexdigest(),native_file=str(p.relative_to(R)),native_file_sha256=hashlib.sha256(p.read_bytes()).hexdigest(),native_function_candidates=len(matches),backward_names=back,backward_occurrences={b:len(re.findall(r'\b'+re.escape(b)+r'\b',raw)) for b in back},discard_candidates=r['discarded_restoration_candidates'],differential='not performed: these complete-Result identities are emission/model laws, not native fidelity gates',source_credit=False,ruling_n='Any reached native mutable-borrow write still needs the per-function native/emission fidelity check before source credit',kani_credit='none; no Kani invocation or PASS consumed',xr_imports=False))
(E/'fidelity-inspection.json').write_text(json.dumps(out,indent=2)+'\n')
print('Inspected',len(out),'emitted bodies; native source-credit claims:',sum(x['source_credit'] for x in out))
