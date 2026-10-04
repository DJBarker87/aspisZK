#!/usr/bin/env python3
"""Generate shared R772 point0/point2 leaf transports and bounded R780 consumers.
This emits Lean source and validates coverage; it does no field evaluation.
"""
import argparse, hashlib, importlib.util, json, re
from pathlib import Path
ROOT=Path('.')
PLAN=ROOT/'.r21-scratch/r748-chosen222-point1-leaf-plan.json'
R762=ROOT/'.r21-scratch/r762-point02-index-inventory/index_inventory.json'
ENTRY=ROOT/'.r21-scratch/r760-pointweight-consumer-plan.json'
R772DIR=ROOT/'docs/research/v8-full-view-zk-20260912/lean/AspisV8R19'
OUT=ROOT/'.r21-scratch/r780-point02-weight-bulk/generated'
PROTO='AspisV8R19.R780Point02WeightPrototype'
BASE='AspisV8R19.R780Point02WeightShared'
# Reuse the already-reviewed R760 arithmetic/index renderer as a parser only.
spec=importlib.util.spec_from_file_location('r760emitter',ROOT/'.r21-scratch/r760-pointweight-consumer-emitter.py')
r760=importlib.util.module_from_spec(spec); spec.loader.exec_module(r760)

def digest(p): return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def source_map():
  plan=json.loads(PLAN.read_text()); rec={x['leaf']:x for x in plan['leaf_records']}
  inv=json.loads(R762.read_text()); zeros=set(inv['indices_by_category']['source_basis_zero/inactive_nonpivot']+inv['indices_by_category']['source_basis_zero/active'])
  raw=sorted({x for xs in plan['leaf_positions_by_pointWeight_index'].values() for x in xs})
  module_map={}; theorem_map={}; rhs_map={}
  allfiles=[R772DIR/'R772Point02DualLeaves.lean', *sorted(R772DIR.glob('R772Point02DualLeavesChunk*.lean'))]
  text={p:p.read_text() for p in allfiles}
  for n in raw:
    original=rec[n]['original']
    for pt in (0,2):
      if original==14:
        name=f'point{pt}_guard14_transport_zero'
        f=allfiles[0]
      elif original==780:
        name=f'point{pt}_candidate780_transport_exact'
        f=allfiles[0]
      else:
        # The exact source plan classifies every other leaf as a generic zero or exact product.
        z=original in zeros
        name=f'p{pt}_transport_{"zero" if z else "exact"}_original_{original}'
        hits=[p for p in allfiles if re.search(rf'theorem\s+{name}\s*:',text[p])]
        if not hits: raise SystemExit(f'missing R772 source theorem {name} for input leaf {n}')
        f=hits[0]
      m=re.search(rf'theorem\s+{name}\s*:\s*([\s\S]*?)\s*:=\s*by',text[f])
      if not m: raise SystemExit(f'cannot parse theorem statement {name}')
      st=m.group(1).strip(); out=st.rsplit('=',1)[1].strip()
      out=re.sub(r'List F','List M',out)
      module_map[(pt,n)]=f.stem; theorem_map[(pt,n)]=name; rhs_map[(pt,n)]=out
  return plan,rec,raw,module_map,theorem_map,rhs_map

def module_imports(modmap):
  return sorted({f'import AspisV8R19.{m}' for m in modmap.values()})

def render_access():
  L=[f'import {PROTO}','',f'namespace {BASE}','open AspisV8R16 AspisV8R17 AspisR19','open AspisR19.TwoSwapSourceTable',f'open {PROTO}','noncomputable section','set_option autoImplicit false','',
    'theorem w0_at (i : Fin 1024) : w0 i.val = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) i := by',
    '  simp [w0, extendFin1024, i.isLt]', '#print axioms w0_at','',
    'theorem w2_at (i : Fin 1024) : w2 i.val = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) i := by',
    '  simp [w2, extendFin1024, i.isLt]', '#print axioms w2_at','end',f'end {BASE}','']
  return '\n'.join(L)

def render_shared_chunk(raw, modmap, theorem_map, rhs_map, ix):
  ns=f'AspisV8R19.R780Point02WeightSharedChunk{ix:02d}'
  imports=[f'import {BASE}',*module_imports({k:v for k,v in modmap.items() if k[1] in raw})]
  L=[*imports,'',f'namespace {ns}','open AspisV8R16 AspisV8R17 AspisR19','open AspisR19.TwoSwapSourceTable',f'open {BASE}',f'open {PROTO}','noncomputable section','set_option autoImplicit false','']
  for n in raw:
    i=records[n]['original']
    L += [f'theorem hpos_leaf_{n} : order.symm ({i} : Fin 1024) = ({n} : Fin 1024) := by decide',f'#print axioms hpos_leaf_{n}','']
    for pt in (0,2):
      name=theorem_map[(pt,n)]; m=modmap[(pt,n)]
      L += [f'theorem w{pt}_leaf_{n} : w{pt} {n} = {rhs_map[(pt,n)]} := by',
        f'  have hs := AspisV8R19.{m}.{name} (F := M)',
        f'  rw [hpos_leaf_{n}] at hs',
        f'  calc w{pt} {n} = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point{pt} j.val) ({n} : Fin 1024) := by',
        f'          simpa using {BASE}.w{pt}_at (i := ({n} : Fin 1024))',
        f'       _ = {rhs_map[(pt,n)]} := hs','',f'#print axioms w{pt}_leaf_{n}','']
  L += ['end',f'end {ns}','']
  return '\n'.join(L)

def leaf_term(pt,n): return rhs_map[(pt,n)]
def gather_rhs(i,parity,pt):
  terms=[]
  for j,pow in LOOP[i]:
    t=f'({leaf_term(pt,2*j+parity)})'
    terms.append(t if pow==0 else f'half^{pow}*{t}')
  return ' + '.join(terms) if terms else '(0:M)'
def nested_rhs(i,parity,pt):
  return re.sub(r'(?<![A-Za-z0-9_])w (\d+)', lambda m: '('+leaf_term(pt,2*int(m.group(1))+parity)+')', NESTED[i])
def raw_gather(i,parity,pt):
  terms=[]
  for j,pow in LOOP[i]:
    t=f'w{pt} (2*{j}+{parity})' if parity else f'w{pt} (2*{j})'
    terms.append(t if pow==0 else f'half^{pow}*{t}')
  return ' + '.join(terms) if terms else '(0:M)'
def raw_nested(i,parity,pt):
  return re.sub(r'(?<![A-Za-z0-9_])w (\d+)',lambda m:f'w{pt} (2*{int(m.group(1))}+{parity})' if parity else f'w{pt} (2*{int(m.group(1))})',NESTED[i])
def target_rhs(n,pt):
  i=n//2
  if n%2==0:
    return f'7*({leaf_term(pt,2*i)}) + 5*({gather_rhs(i,0,pt)}) - 5*({leaf_term(pt,2*i+1)})'
  return f'-5*(({leaf_term(pt,2*i)}) - ({nested_rhs(i,0,pt)})) + 7*({leaf_term(pt,2*i+1)}) + 5*({gather_rhs(i,1,pt)})'
def raw_rhs(n,pt):
  i=n//2
  if n%2==0:
    return f'7*w{pt} (2*{i}) + 5*({raw_gather(i,0,pt)}) - 5*w{pt} (2*{i}+1)'
  return f'-5*(w{pt} (2*{i}) - ({raw_nested(i,0,pt)})) + 7*w{pt} (2*{i}+1) + 5*({raw_gather(i,1,pt)})'
def needed_names(n,pt):
  i=n//2; xs=set()
  for j,_ in LOOP[i]:
    xs.add(2*j+(n%2))
    if n%2:
      for k,_ in LOOP[j]: xs.add(2*k)
  xs|={2*i,2*i+1}
  return [f'w{pt}_leaf_{x}' for x in sorted(xs)]
def render_consumer(nums,pt,modmap,raw_inputs,chunk_ix):
  # R748 modules exactly match the source schedules already used by R760.
  shared_ix=sorted({raw_chunk_by_leaf[n] for n in raw_inputs})
  imports=[f'import {BASE}',*[f'import AspisV8R19.R780Point02WeightSharedChunk{i:02d}' for i in shared_ix],'import AspisV8R19.R748FiniteGatherSchedules','import AspisV8R19.R748SchedulePrototype']
  imports += [f'import AspisV8R19.R748GatherLoop{i:02d}' for i in range(8)]
  imports += [f'import AspisV8R19.R748GatherExpand{i:02d}' for i in range(8)]
  imports += [f'import AspisV8R19.R748GatherNested{i:02d}' for i in range(5)]
  L=[*imports,'',f'namespace AspisV8R19.R780Point02WeightChunk{chunk_ix:02d}P{pt}','open AspisV8R16 AspisV8R17 AspisR19',f'open {BASE}',f'open {PROTO}',*[f'open AspisV8R19.R780Point02WeightSharedChunk{i:02d}' for i in shared_ix],'open AspisV8R17','open AspisV8R19.R742SourceObservationHom','open AspisV8R19.R748FiniteGatherSchedules','open AspisV8R19.R748SchedulePrototype']
  L += [f'open AspisV8R19.R748GatherExpand{i:02d}' for i in range(8)]
  L += [f'open AspisV8R19.R748GatherNested{i:02d}' for i in range(5)]
  L += ['noncomputable section','set_option autoImplicit false','set_option maxRecDepth 4096','']
  w=f'w{pt}'; point=f'point{pt}'; pw=f'pw{pt}'
  for n in nums:
    i=n//2; odd=n%2
    sched=['gatherGather'+str(i),'gather'+str(i)] if odd else ['gather'+str(i)]
    L += [f'theorem pw{pt}_{n:04d} : {pw} {n} = {target_rhs(n,pt)} := by',
      f'  change sourceChordTranspose half {w} 7 5 (-5) {n} = _',
      f"  unfold sourceChordTranspose interleave {'chordDualOdd' if odd else 'chordDualEven'}",
      '  simp only [Nat.reduceMod, Nat.reduceDiv, ↓reduceIte]']
    if odd: L += ['  simp only [one_ne_zero, if_false]']
    L += [f'  have hwe (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => {w} (2*i)) i = {w} (2*i) := by',
      '    unfold zeroExtend; rw [if_pos hi]',
      f'  have hwo (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => {w} (2*i+1)) i = {w} (2*i+1) := by',
      '    unfold zeroExtend; rw [if_pos hi]',
      f'  rw [{", ".join(sched)}]']
    ev,od=r760.lane_indices(n)
    L += [f'  rw [{", ".join([f"hwe {x} (by omega)" for x in ev]+[f"hwo {x} (by omega)" for x in od])}]',f'  change {raw_rhs(n,pt)} = {target_rhs(n,pt)}',f'  rw [{", ".join(needed_names(n,pt))}]',f'#print axioms pw{pt}_{n:04d}','']
  return '\n'.join(L+['end',f'end AspisV8R19.R780Point02WeightChunk{chunk_ix:02d}P{pt}',''])

# Initialize cross-file renderer tables.
PLAN_DATA,records,raw_inputs,modmap,theorem_map,rhs_map=source_map()
raw_chunk_by_leaf={n:i//32 for i,n in enumerate(raw_inputs)}
r760.LOOP=r760.loops(); r760.NESTED={}
pat=re.compile(r'lemma gatherGather(\d+).*?=\s*(.*?)\s*:= by',re.S)
for f in r760.NESTED_SOURCES:
 for m in pat.finditer(f.read_text()): r760.NESTED[int(m.group(1))]=re.sub(r'\s+',' ',m.group(2)).strip()
LOOP=r760.LOOP; NESTED=r760.NESTED

def main():
 ap=argparse.ArgumentParser();ap.add_argument('--check',action='store_true');ap.add_argument('--weight-chunk',type=int,default=0);ap.add_argument('--start-index',type=int);ap.add_argument('--count',type=int,default=4);args=ap.parse_args()
 needed=sorted(PLAN_DATA['needed_pointWeight_indices'])
 assert len(needed)==343 and set(raw_inputs)==set(x for xs in PLAN_DATA['leaf_positions_by_pointWeight_index'].values() for x in xs)
 for n in needed:
  i=n//2; assert i in LOOP,(n,i)
  assert all(2*j+n%2 in raw_inputs for j,_ in LOOP[i])
  if n%2: assert i in NESTED
 start=args.start_index if args.start_index is not None else args.weight_chunk*4
 group=needed[start:start+args.count]
 if not group: raise SystemExit(f'empty weight chunk {args.weight_chunk}')
 outputs={'R780Point02WeightShared.lean':render_access()}
 for ix in range((len(raw_inputs)+31)//32):
  leaf_group=raw_inputs[ix*32:(ix+1)*32]
  outputs[f'R780Point02WeightSharedChunk{ix:02d}.lean']=render_shared_chunk(leaf_group,modmap,theorem_map,rhs_map,ix)
 for pt in (0,2):
  used=set()
  for n in group:
   i=n//2
   used|={2*i,2*i+1}
   for j,_ in LOOP[i]:
    used.add(2*j+n%2)
    if n%2:
     used.update(2*k for k,_ in LOOP[j])
  outputs[f'R780Point02WeightChunk{args.weight_chunk:02d}P{pt}.lean']=render_consumer(group,pt,modmap,sorted(used),args.weight_chunk)
 # Plan is authoritative for 343 positions and 519 raw coordinates.
 coverage={'schema':'r780-point02-weight-bulk-coverage-v1','pointWeight_indices':needed,'pointWeight_count':len(needed),'raw_leaf_positions':sorted(raw_inputs),'raw_leaf_count':len(raw_inputs),'weight_chunk':args.weight_chunk,'start_index':start,'first_chunk':group,'chunk_size':args.count,'sources':{str(p):digest(p) for p in [PLAN,ENTRY,R762,R772DIR/'R771Point02Transport.lean',R772DIR/'R772Point02DualLeaves.lean',*sorted(R772DIR.glob('R772Point02DualLeavesChunk*.lean'))]},'generated_sha256':{k:hashlib.sha256(v.encode()).hexdigest() for k,v in outputs.items()},'status':'Generated source only; no numeric field evaluation; pointWeight expressions are exact finite gather and R772 leaf outputs.'}
 outputs['COVERAGE.json']=json.dumps(coverage,indent=2,sort_keys=True)+'\n'
 if args.check:
  for k,v in outputs.items():
   p=OUT/k
   if not p.exists() or p.read_text()!=v: raise SystemExit('mismatch '+str(p))
  return
 OUT.mkdir(parents=True,exist_ok=True)
 for k,v in outputs.items(): (OUT/k).write_text(v)
if __name__=='__main__': main()
