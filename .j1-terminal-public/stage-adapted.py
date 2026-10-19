from pathlib import Path
import importlib.util,json,shutil
B=Path('/home/dombarker/project-offloads');w=B/'aspis-r1-j1a-terminal-public-adapted-20261016';j=B/'aspis-r1-j1a-terminal-public-joint-20261016';t=B/'aspis-r1-j1a-terminal-proof-20261016';c=B/'aspis-r1-j1a-terminal-caller-adapted-20261016'
s=importlib.util.spec_from_file_location('r',w/'runner.py');r=importlib.util.module_from_spec(s);s.loader.exec_module(r)
base=j/'external-inputs-joint.json';d,_=r.verify_snapshot(base)
removed={n:d['modules'].pop(n) for n in ['AspisR1TerminalValidator.Types','AspisR1TerminalValidator.FunsExternal','AspisR1TerminalValidator.Funs','ExtractedTerminalEquality','ExtractedTerminalWithdrawalSuccess','ExtractedTerminalCallerBridge']}
assert not any(dep in removed for v in d['modules'].values() for dep in v['imports'])
d['provenance_files'][str(base)]=r.sha(base);d['scope']='Prior exact joint snapshot minus only six Terminal-dependent modules. One-sided Terminal fourteen-code instance naming adapter; original sources and objects unchanged. Affected modules checked in this workspace.'
r.dump(w/'external-inputs-public.json',d);r.dump(w/'removed-terminal-pins.json',removed)
modules={};order=['AspisR1TerminalValidator.Types','TerminalPaymentDiscriminantAudit','AspisR1TerminalValidator.FunsExternal','AspisR1TerminalValidator.Funs','TerminalGeneratedAudit','ExtractedTerminalEquality','ExtractedTerminalWithdrawalSuccess','ExtractedTerminalCallerBridge','ExtractedWithdrawalCallerCarrier','ExtractedWithdrawalCallerPublic','ExtractedTerminalPublicBridge']
mt=json.loads((t/'sources/SOURCE-MANIFEST.json').read_text());mc=json.loads((c/'sources/SOURCE-MANIFEST.json').read_text())
for n in order:
 f=w/'sources'/(n.replace('.','/')+'.lean')
 if n in mt['modules'] and n!='AspisR1TerminalValidator.Types':
  x=mt['modules'][n];src=t/'sources'/x['stage_as'];assert r.sha(src)==x['source_sha256'];f.parent.mkdir(parents=True,exist_ok=True);shutil.copy2(src,f)
 elif n=='ExtractedTerminalCallerBridge':
  x=mc['modules'][n];src=c/'sources'/x['stage_as'];assert r.sha(src)==x['source_sha256'];shutil.copy2(src,f)
 source=('lean/bridge-terminal-public-20261016/AspisR1TerminalValidator/Types.lean' if n=='AspisR1TerminalValidator.Types' else 'diagnostic/'+n+'.lean' if n in ['TerminalGeneratedAudit','TerminalPaymentDiscriminantAudit'] else 'lean/'+n+'.lean')
 modules[n]={'stage_as':str(f.relative_to(w/'sources')),'source':(mt['modules'][n]['source'] if n in mt['modules'] and n!='AspisR1TerminalValidator.Types' else 'docs/research/100bit-spend-path-20261013/'+source),'source_sha256':r.sha(f),'source_revision':'2ff2ea148 plus Terminal/public naming adapter and direct composition','imports':r.imports(f),'role':'Focused affected source check after one-sided naming adapter','axiom_requests':{'TerminalPaymentDiscriminantAudit':1,'AspisR1TerminalValidator.FunsExternal':2,'TerminalGeneratedAudit':5,'ExtractedTerminalEquality':4,'ExtractedTerminalWithdrawalSuccess':1,'ExtractedTerminalCallerBridge':10,'ExtractedWithdrawalCallerCarrier':8,'ExtractedWithdrawalCallerPublic':2,'ExtractedTerminalPublicBridge':2}.get(n,0)}
modules['AspisR1TerminalValidator.Funs']['source']='docs/research/100bit-spend-path-20261013/lean/extracted-terminal-validator-20261016/AspisR1TerminalValidator/Funs.lean'
modules['TerminalGeneratedAudit']['source']='diagnostic/TerminalGeneratedAudit.lean'
r.dump(w/'sources/SOURCE-MANIFEST.json',{'format':2,'modules':modules,'topological_order':order,'groups':{}});r.staged(w)
print(json.dumps({'snapshot_sha256':r.sha(w/'external-inputs-public.json'),'targets':order},indent=2))
