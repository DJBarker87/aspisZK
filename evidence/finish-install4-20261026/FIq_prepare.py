from pathlib import Path
import re,json,hashlib
R=Path(__file__).resolve().parents[2]; P=R/'evidence/finish-install4-20261026'; L=R/'lean'
D=R/'docs/research/100bit-spend-path-20261013/evidence/terminal-v4-external-model-integration-20261019/sources'
S=D/'FunsWithModeledExternal.lean'; s=S.read_text()
# Generated declaration blocks start at their source comments and contain one declaration.
body=s.split('namespace AspisR1SelectedMaskProbe\n',1)[1].split('\nend AspisR1SelectedMaskProbe')[0]
blocks=re.split(r'(?=^/-- )',body,flags=re.M)
items=[]
for b in blocks:
 clean=re.sub(r'/\*.*?\*/|/--.*?-/', '', b,flags=re.S)
 m=re.search(r'\b(?:def|impl_def|abbrev)\s+([^\s(:]+)',clean)
 if m:items.append((m[1],b))
by=dict(items); names=set(by); root='pool_v1.pair_forest_semantic_terminal.r0.Public.terminal_qm31'
refs={n:set(re.findall(r'[\w]+(?:\.[\w]+)+',re.sub(r'/--.*?-/', '', b,flags=re.S)))&names for n,b in items}
seen=set();todo=[root]
while todo:
 n=todo.pop()
 if n in seen:continue
 seen.add(n);todo+=list(refs[n]-seen)
selected=[(n,b) for n,b in items if n in seen]
(P/'FIq_native-selection.json').write_text(json.dumps({'source':str(S.relative_to(R)),'sha256':hashlib.sha256(s.encode()).hexdigest(),'declarations':len(selected),'names':[n for n,b in selected]},indent=2)+'\n')
# Keep all native type definitions, fresh namespace and list iterator representation.
t=R/'docs/research/100bit-spend-path-20261013/evidence/terminal-v4-current-soundness-packet-20261019/supporting/generated-current-v4/AspisR1SelectedMaskProbe/Types.lean'
x=t.read_text().replace('import AspisR1SelectedMaskProbe.TypesExternal','').replace('AspisR1SelectedMaskProbe','FIq_Native')
x=re.sub(r'^set_option max(?:Heartbeats|RecDepth).*\n','',x,flags=re.M)
x=x.replace('namespace FIq_Native','namespace FIq_Native\nabbrev core.array.iter.IntoIter (T : Type) (_N : Usize) := List T',1)
(L/'FIq_NativeTypes.lean').write_text(x)
# Split only at declaration boundaries. No source semantic edits.
chunks=[];current=[];size=0
for n,b in selected:
 if size+len(b)>22000 and current:chunks.append(current);current=[];size=0
 current.append((n,b));size+=len(b)
if current:chunks.append(current)
for i,ch in enumerate(chunks,1):
 prev='FIq_NativeExternal' if i==1 else f'FIq_Native{i-1:02}'
 out=f'import {prev}\nopen Aeneas Aeneas.Std Result ControlFlow Error\nset_option linter.unusedVariables false\nnoncomputable section\nnamespace FIq_Native\n'+''.join(b for n,b in ch)+'\nend FIq_Native\n'
 (L/f'FIq_Native{i:02}.lean').write_text(out)
print('selected',len(selected),'chunks',len(chunks))
# External calls required by selected computation (excluding generated types).
external=(D/'FunsExternalV5.lean').read_text()
for n in re.findall(r'axiom\s+([^\s(:]+)',external):
 if any(n in b for _,b in selected):print('EXTERNAL',n)
