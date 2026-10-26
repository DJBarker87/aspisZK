from pathlib import Path
import hashlib,json,re
P=Path(__file__).resolve().parent;R=P.parents[1]
receipts=[]
for d in sorted(P.glob('FIr_[0-9][0-9][0-9]')):
 r=json.loads((d/'receipt.json').read_text());r['directory']=d.name;receipts.append(r)
required={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'}
for r in receipts:
 assert r['limits']==required,(r['attempt'],r['limits'])
 assert str(r['swaps'])=='0',r['attempt']
 assert '-M7000' in r['command']
checks=[]
for f in sorted((R/'lean').glob('FIr_*.lean')):
 sha=hashlib.sha256(f.read_bytes()).hexdigest()
 matched=[r['attempt'] for r in receipts if r['exit_status']==0 and r['source_hashes'].get(f.name)==sha]
 assert matched,('no exact-source passing receipt',f.name,sha)
 checks.append(dict(module=f.stem,sha256=sha,passing=matched))
 s=f.read_text()
 assert not re.search(r'\b(sorry|admit|axiom|native_decide)\b|set_option\s+(maxHeartbeats|maxRecDepth)',s),f.name
# Final audit is a fresh missing closure artifact, not a package replay.
expected=json.loads((P/'FIr_axiom-targets.json').read_text())['targets']
audit=(P/'FIr_100/stdout.log').read_text()
for name in expected:
 assert "'"+name+"'" in audit,name
reports=re.findall(r"'([^']+)' (?:depends on axioms:\s*\[([^]]*)\]|does not depend on any axioms)",audit)
for name,axioms in reports:
 assert set(re.findall(r'[A-Za-z_][A-Za-z_.]*',axioms))<={'propext','Classical.choice','Quot.sound'},(name,axioms)
x=dict(charged_lean_attempts=100,compiler_starts=len(receipts),kani_runs=0,passing=sum(r['exit_status']==0 for r in receipts),failed=sum(r['exit_status']!=0 for r in receipts),preflight_attempts=['FIr_001'],modules=checks,axiom_reports=len(reports),accepted_axioms=['propext','Classical.choice','Quot.sound'],caps=required,swaps=0,final_combined_audit_exit=1,final_combined_audit_error='FIr_100: ill-formed syntax in auxiliary private-name print command; all102 public target reports and native terminal report precede the error. No combined closure pass claimed.',final_top_receipt='FIr_094',final_nonvacuity_receipt='FIr_095',final_statements_receipt='FIr_097',private_print_audit_complete=False)
(P/'FIr_validation.json').write_text(json.dumps(x,indent=2)+'\n')
print(json.dumps({k:v for k,v in x.items() if k!='modules'},indent=2))
