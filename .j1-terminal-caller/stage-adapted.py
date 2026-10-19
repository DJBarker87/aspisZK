from pathlib import Path
import importlib.util,json
w=Path('/home/dombarker/project-offloads/aspis-r1-j1a-terminal-caller-adapted-20261016');j=Path('/home/dombarker/project-offloads/aspis-r1-j1a-terminal-caller-joint-20261016')
s=importlib.util.spec_from_file_location('r',w/'runner.py');r=importlib.util.module_from_spec(s);s.loader.exec_module(r)
base=j/'external-inputs-carrier.json';d,_=r.verify_snapshot(base)
removed={n:d['modules'].pop(n) for n in ['AspisR1WithdrawalCaller.Types','AspisR1WithdrawalCaller.Funs','ExtractedWithdrawalCallerSuccess']}
assert not any(dep in removed for v in d['modules'].values() for dep in v['imports'])
d['roots']=[x for x in d['roots'] if x['name']!='caller_checked'];d['provenance_files'][str(base)]=r.sha(base);d['scope']='Exact prior snapshot with only three old Caller modules removed. New one-sided two-code Types naming adapter and unchanged Funs/Success are focused own targets; Terminal and original caches remain untouched.'
r.dump(w/'external-inputs-terminal.json',d);r.dump(w/'removed-original-caller-pins.json',removed)
mods={};names=['AspisR1WithdrawalCaller.Types','AspisR1WithdrawalCaller.Funs','ExtractedWithdrawalCallerSuccess','WithdrawalCallerKindAudit','ExtractedTerminalCallerBridge']
paths=['lean/bridge-withdrawal-caller-terminal-20261016/AspisR1WithdrawalCaller/Types.lean','lean/extracted-withdrawal-caller-20261016/AspisR1WithdrawalCaller/Funs.lean','lean/ExtractedWithdrawalCallerSuccess.lean','diagnostic/WithdrawalCallerKindAudit.lean','lean/ExtractedTerminalCallerBridge.lean']
for n,cp in zip(names,paths):
 f=w/'sources'/(n.replace('.','/')+'.lean');mods[n]={'stage_as':str(f.relative_to(w/'sources')),'source_sha256':r.sha(f),'imports':r.imports(f),'source':'docs/research/100bit-spend-path-20261013/'+cp,'source_revision':'43c9991fd plus new exact Terminal/Caller transport and two-code naming adapter','role':'Focused actual generated computation transport','axiom_requests':{'ExtractedWithdrawalCallerSuccess':4,'WithdrawalCallerKindAudit':2,'ExtractedTerminalCallerBridge':10}.get(n,0)}
r.dump(w/'sources/SOURCE-MANIFEST.json',{'format':2,'modules':mods,'topological_order':names,'groups':{}});r.staged(w)
print(json.dumps({'snapshot_sha256':r.sha(w/'external-inputs-terminal.json'),'targets':names},indent=2))
