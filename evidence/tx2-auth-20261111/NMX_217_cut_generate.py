"""Literal CPS factor of the pinned emitted safe reference. Children stay folded."""
from pathlib import Path
import argparse,json,re,hashlib
E=Path(__file__).resolve().parent;R=E.parent/'native-decref-20261028';p=R/'NCV_generated/NCV_Reference/Funs.lean';text=p.read_text();pin=json.loads((R/'NCV_DELIVERY.json').read_text())['lean/NCV_Reference/Funs.lean']['source_sha256'];assert hashlib.sha256(text.encode()).hexdigest()==pin
start=text.index('def decode_lane_ref\n');stop=text.index('\n/-- [ncv_reference::option_item]',start);body=text[start:stop];body=body[body.index(':= do')+5:];lines=body.splitlines();ind=lambda l:len(l)-len(l.lstrip())
patterns=[('finish','if next_leaf_index = 0#u64'),('frontier','let r1 ←'),('digest','let r ←'),('counter','let next_leaf_index ←'),('tree','let tree ←'),('master','let master ←'),('header','let s ←')]
params={
'finish':[('b','Slice U8'),('master','Array U8 32#usize'),('i2','U8'),('next_leaf_index','U64'),('val','Array U32 8#usize'),('val1','Array (Array U32 8#usize) 20#usize')],
'frontier':[('b','Slice U8'),('master','Array U8 32#usize'),('i2','U8'),('tree','Slice U8'),('next_leaf_index','U64'),('val','Array U32 8#usize')],
'digest':[('b','Slice U8'),('master','Array U8 32#usize'),('i2','U8'),('tree','Slice U8'),('next_leaf_index','U64')],
'counter':[('b','Slice U8'),('master','Array U8 32#usize'),('i2','U8'),('tree','Slice U8')],
'tree':[('b','Slice U8'),('master','Array U8 32#usize'),('i2','U8')],
'master':[('b','Slice U8'),('i2','U8')],
'header':[('b','Slice U8')],
'run':[('b','Slice U8')]}
regions={}
for name,pat in patterns:
 hits=[i for i,l in enumerate(lines) if l.strip().startswith(pat)];assert len(hits)==1,(name,hits)
 i=hits[0];base=ind(lines[i]);j=i+1
 while j<len(lines) and (not lines[j].strip() or ind(lines[j])>=base):j+=1
 regions[name]=(i,j)
regions['run']=(0,len(lines))
order=[n for n,_ in patterns]+['run'];parts=['import NCV_Reference.Funs\nset_option autoImplicit false\nnamespace NMX_R3_LaneCuts\nopen Aeneas Aeneas.Std Result NCV_Reference\n']
for pos,name in enumerate(order):
 i,j=regions[name];chunk=lines[i:j].copy();base=ind(next(l for l in chunk if l.strip()))
 if pos:
  prev=order[pos-1];a,b=regions[prev];assert i<=a<b<=j,(name,prev)
  args=' '.join(n for n,_ in params[prev]);chunk[a-i:b-i]=[' '*ind(lines[a])+'NMX_R3_LaneCuts.'+prev+' '+args]
 code='\n'.join('  '+l[base:] if l.strip() else '' for l in chunk)
 code=re.sub(r'(?<![\w.])(equal|zero|bytes32|word64|digest|decode_frontier|eq_digest|EMPTY)\b',lambda m:'NCV_Reference.'+m[0],code)
 ps=' '.join('('+n+' : '+t+')' for n,t in params[name]);parts.append('\ndef '+name+' '+ps+' : Result (core.result.Result NCV_Reference.Lane Unit) := do\n'+code+'\n')
parts.append('''
theorem factor (b : Slice U8) : run b = NCV_Reference.decode_lane_ref b := by
 rfl
#print axioms factor
end NMX_R3_LaneCuts
''');out=''.join(parts)
ap=argparse.ArgumentParser();ap.add_argument('--check',action='store_true');a=ap.parse_args();dest=E/'NMX_R3_LaneCuts.lean'
manifest={'source':str(p),'source_sha256':pin,'regions':regions,'params':params,'source_order':list(reversed(order)),'changes':'literal subtree replacement by a definition with exactly the free local arguments; original child identifiers qualified to NCV_Reference without changing their owners or arguments','proof':'factor checked by Lean definitional equality; no child/loop body unfolding requested','sha256':hashlib.sha256(out.encode()).hexdigest()}
manifest=json.loads(json.dumps(manifest))
if a.check:assert dest.read_text()==out and json.loads((E/'NMX_R3_LANE_CUTS.json').read_text())==manifest
else:dest.write_text(out);(E/'NMX_R3_LANE_CUTS.json').write_text(json.dumps(manifest,indent=2)+'\n')
print(json.dumps({'check':a.check,'literal_cuts':len(order),'source_sha256':pin}))
