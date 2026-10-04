#!/usr/bin/env python3
"""Render fixed-witness finite pointWeight proofs from approved leaf/schedule facts.
This program only emits/checks source. It never invokes Lean or computes field sums.
"""
from pathlib import Path
import argparse, hashlib, json, re
ROOT=Path('.')
PLAN=ROOT/'.r21-scratch/r748-chosen222-point1-leaf-plan.json'
OUT=ROOT/'.r21-scratch/r760-pointweight-consumer-generated'
SCHEDULES=[ROOT/'docs/research/v8-full-view-zk-20260912/lean/AspisV8R19/R748FiniteGatherSchedules.lean', ROOT/'.r21-scratch/r748-gather-schedule-generator/PrototypeDensest255.lean']+sorted((ROOT/'.r21-scratch/r748-gather-schedule-generator/generated').glob('R748GatherLoop*.lean'))+sorted((ROOT/'.r21-scratch/r748-gather-schedule-generator/generated').glob('R748GatherExpand*.lean'))
GUARDS=sorted((ROOT/'docs/research/v8-full-view-zk-20260912/lean/AspisV8R19').glob('Point1GuardedChunk*.lean'))
TRANS=sorted((ROOT/'.r21-scratch/r759-point1-transport-generated').glob('R759Point1TransportChunk*.lean'))
NESTED_SOURCES=[ROOT/'docs/research/v8-full-view-zk-20260912/lean/AspisV8R19/R748FiniteGatherSchedules.lean', ROOT/'.r21-scratch/r748-gather-schedule-generator/PrototypeDensest255.lean']+sorted((ROOT/'.r21-scratch/r748-gather-schedule-generator/generated').glob('R748GatherNested*.lean'))
R748=ROOT/'docs/research/v8-full-view-zk-20260912/lean/AspisV8R19/R748JointWitnessPointEntry.lean'

def digest(p): return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def loops():
  d={}
  pat=re.compile(r'lemma loop(\d+)\s*:\s*indexLoop 10 \1 0\s*=\s*some\s*(\[[^]]*\])',re.S)
  for p in SCHEDULES:
    for m in pat.finditer(p.read_text()):
      d[int(m.group(1))]=[(int(a),int(b)) for a,b in re.findall(r'\((\d+),(\d+)\)',m.group(2))]
  return d

def leaves():
  d={}
  # nonzero leaves deliberately preserve the emitted `b + 576` expression.
  pat=re.compile(r'lemma transport_leaf_(\d+)\s*:\s*w\s+(\d+)\s*=\s*(.*?)\s*:= by',re.S)
  for p in TRANS:
    for m in pat.finditer(p.read_text()): d[int(m.group(2))]=(f'transport_leaf_{m.group(1)}',re.sub(r'\s+',' ',m.group(3)).strip())
  pat=re.compile(r'lemma w_guarded_leaf_(\d+)\s*:\s*\n?\s*R748JointWitnessPointEntry\.w\s+(\d+)\s*=\s*(.*?)\s*:= by',re.S)
  for p in GUARDS:
    for m in pat.finditer(p.read_text()): d[int(m.group(2))]=(f'w_guarded_leaf_{m.group(1)}',re.sub(r'\s+',' ',m.group(3)).replace('R748JointWitnessPointEntry.M','M').strip())
  # Reuse the twenty finite leaves already proved by R748 instead of re-emitting them.
  pat=re.compile(r'lemma w_(\d+)\s*:\s*w\s+\1\s*=\s*(.*?)\s*:= by',re.S)
  for m in pat.finditer(R748.read_text()): d[int(m.group(1))]=(f'w_{m.group(1)}',re.sub(r'\s+',' ',m.group(2)).strip())
  return d

def raww(j, parity):
  return f'w (2*{j})' if parity==0 else f'w (2*{j}+1)'
def rawterm(p, j, parity):
  x=raww(j,parity)
  return x if p==0 else f'((1073741824:M)^{p})*{x}'
def term(p, leaf):
  rhs=LEAF[leaf][1]
  return rhs if p==0 else f'((1073741824:M)^{p})*({rhs})'
def gather_raw(i, parity):
  return ' + '.join(rawterm(pow, j, parity) for j,pow in LOOP[i]) or '(0:M)'
def gather(i, parity):
  return ' + '.join(term(pow, 2*j+parity) for j,pow in LOOP[i]) or '(0:M)'
def nested_raw(i, parity):
  rhs=re.sub(r'(?<![A-Za-z0-9_])half(?![A-Za-z0-9_])', '(1073741824:M)', NESTED[i])
  return re.sub(r'(?<![A-Za-z0-9_])w (\d+)', lambda m: raww(int(m.group(1)),parity), rhs)
def nested(i, parity):
  rhs=re.sub(r'(?<![A-Za-z0-9_])half(?![A-Za-z0-9_])', '(1073741824:M)', NESTED[i])
  return re.sub(r'(?<![A-Za-z0-9_])w (\d+)', lambda m: '('+LEAF[2*int(m.group(1))+parity][1]+')', rhs)
def raw_rhs(n):
  i=n//2
  if n%2==0:
    return f'7*{raww(i,0)} + 5*({gather_raw(i,0)}) - 5*{raww(i,1)}'
  return f'-5*({raww(i,0)} - ({nested_raw(i,0)})) + 7*{raww(i,1)} + 5*({gather_raw(i,1)})'
def rhs(n):
  i=n//2
  if n%2==0:
    return f'7*({LEAF[2*i][1]}) + 5*({gather(i,0)}) - 5*({LEAF[2*i+1][1]})'
  return f'-5*(({LEAF[2*i][1]}) - ({nested(i,0)})) + 7*({LEAF[2*i+1][1]}) + 5*({gather(i,1)})'
def lane_indices(n):
  i=n//2
  even={i}; odd={i}
  for j,_ in LOOP[i]:
    (odd if n%2 else even).add(j)
  if n%2:
    even |= {int(x) for x in re.findall(r'(?<![A-Za-z0-9_])w (\d+)', NESTED[i])}
  return sorted(even),sorted(odd)
def needed_names(n):
  i=n//2; xs=set()
  for j,_ in LOOP[i]:
    xs.add(2*j+(n%2))
    if n%2:
      for k,_ in LOOP[j]: xs.add(2*k)
  xs|={2*i,2*i+1}
  return [LEAF[x][0] for x in sorted(xs)]
def render_chunk(chunk, ns):
  nums=chunk
  imports=['import AspisV8R19.R748JointWitnessPointEntry',
           *[f'import AspisV8R19.{p.stem}' for p in GUARDS],
           *[f'import AspisV8R19.{p.stem}' for p in TRANS],
           'import AspisV8R19.R748FiniteGatherSchedules',
           *[f"import AspisV8R19.{('R748SchedulePrototype' if p.stem == 'PrototypeDensest255' else p.stem)}" for p in SCHEDULES[1:]],
           'import AspisV8R19.R748GatherNested00', 'import AspisV8R19.R748GatherNested01',
           'import AspisV8R19.R748GatherNested02', 'import AspisV8R19.R748GatherNested03', 'import AspisV8R19.R748GatherNested04']
  # Imports are prospective: root review must replace scratch module locations by canonical modules once promoted.
  s='\n'.join(imports)+'\n\nnamespace '+ns+'\nopen AspisV8R16 AspisV8R17 AspisR19\nopen AspisV8R19.R748JointWitnessPointEntry\nopen AspisV8R19.R740SparsePointObservation\nopen AspisV8R19.R748SchedulePrototype\nopen AspisV8R19.R748GatherExpand00 AspisV8R19.R748GatherExpand01 AspisV8R19.R748GatherExpand02 AspisV8R19.R748GatherExpand03 AspisV8R19.R748GatherExpand04 AspisV8R19.R748GatherExpand05 AspisV8R19.R748GatherExpand06 AspisV8R19.R748GatherExpand07\nopen AspisV8R19.R748GatherNested00 AspisV8R19.R748GatherNested01 AspisV8R19.R748GatherNested02 AspisV8R19.R748GatherNested03 AspisV8R19.R748GatherNested04\nopen AspisR19.R754Point1GuardedLeaves\nopen AspisR19.R759Point1TransportLeaves\nopen AspisV8R19.R748FiniteGatherSchedules\nnoncomputable section\nset_option maxRecDepth 4096\n\n'
  for n in nums:
    i=n//2; isodd=n%2
    schedule=['gatherGather'+str(i),'gather'+str(i)] if isodd else ['gather'+str(i)]
    # Existing R748 values are reused, never re-emitted.
    s+=f'/-- finite source-only pointWeight expansion at {n}; no field reduction --/\nlemma pw_{n:04d} : pw {n} = {rhs(n)} := by\n'
    s+='  unfold pw pointWeight sourceChordTranspose\n'
    s+=f"  unfold interleave {'chordDualOdd' if isodd else 'chordDualEven'}\n"
    s+='  simp only [Nat.reduceMod, Nat.reduceDiv, ↓reduceIte]\n'
    if isodd: s+='  simp only [one_ne_zero, if_false]\n'
    s+='  have hwe (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => extendFin1024 (transportDual TwoSwapSourceTable.inactive 1023 TwoSwapSourceTable.order (fun j => sourcePointBasis point j.val)) (2*i)) i = w (2*i) := by\n    unfold zeroExtend\n    rw [if_pos hi]\n    unfold w\n    rfl\n'
    s+='  have hwo (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => extendFin1024 (transportDual TwoSwapSourceTable.inactive 1023 TwoSwapSourceTable.order (fun j => sourcePointBasis point j.val)) (2*i+1)) i = w (2*i+1) := by\n    unfold zeroExtend\n    rw [if_pos hi]\n    unfold w\n    rfl\n'
    s+='  rw ['+', '.join(schedule)+']\n'
    ev,od=lane_indices(n)
    s+='  rw ['+', '.join([f'hwe {x} (by omega)' for x in ev]+[f'hwo {x} (by omega)' for x in od])+']\n'
    s+=f'  change {raw_rhs(n)} = {rhs(n)}\n'
    s+='  rw ['+', '.join(needed_names(n))+']\n'
    s+=f'#print axioms pw_{n:04d}\n\n'
  return s+'end\nend '+ns+'\n'
def main():
  global LOOP,LEAF,NESTED
  p=json.loads(PLAN.read_text()); LOOP=loops(); LEAF=leaves()
  NESTED={}
  pat=re.compile(r'lemma gatherGather(\d+).*?=\s*(.*?)\s*:= by',re.S)
  for f in NESTED_SOURCES:
    for m in pat.finditer(f.read_text()): NESTED[int(m.group(1))]=re.sub(r'\s+',' ',m.group(2)).strip()
  need=sorted(p['needed_pointWeight_indices']); reuse={0,3,188,191}; need=[n for n in need if n not in reuse]
  for n in need:
    i=n//2
    assert i in LOOP,('no outer loop',n,i)
    assert all(2*j+(n%2) in LEAF for j,_ in LOOP[i])
    if n%2: assert i in NESTED
  # The densest value is proved only in the dedicated prototype; chunks contain the other 338 values.
  densest=max(need,key=lambda n:len(needed_names(n)))
  chunk_values=[n for n in need if n != densest]
  groups=[chunk_values[k:k+32] for k in range(0,len(chunk_values),32)]
  outputs={'R760PointWeightPrototype.lean':render_chunk([densest],'AspisV8R19.R760PointWeightPrototype')}
  for ix,g in enumerate(groups): outputs[f'R760PointWeightChunk{ix:02d}.lean']=render_chunk(g,f'AspisV8R19.R760PointWeightChunk{ix:02d}')
  manifest={'schema':'r760-pointweight-emitter-v1','input_plan_sha256':digest(PLAN),'emitter_sha256':digest(__file__),'reused_pw':[0,3,188,191],'generated_pointWeight_count':len(need),'chunk_pointWeight_count':len(chunk_values),'densest_pointWeight_index':densest,'densest_leaf_count':len(needed_names(densest)),'source_sha256':{str(p):digest(p) for p in [PLAN,*SCHEDULES,*NESTED_SOURCES,*GUARDS,*TRANS]},'outputs':{k:hashlib.sha256(v.encode()).hexdigest() for k,v in outputs.items()},'status':'Source-only generated candidates. Do not compile before lead reviews prototype and only after named generated schedule imports are canonical and focused-green.'}
  outputs['MANIFEST.json']=json.dumps(manifest,indent=2,sort_keys=True)+'\n'
  if ARGS.check:
    for k,v in outputs.items():
      if not (OUT/k).exists() or (OUT/k).read_text()!=v: raise SystemExit('mismatch: '+str(OUT/k))
    return
  OUT.mkdir(parents=True,exist_ok=True)
  for k,v in outputs.items(): (OUT/k).write_text(v)
if __name__=='__main__':
  ap=argparse.ArgumentParser(); ap.add_argument('--check',action='store_true'); ARGS=ap.parse_args(); main()
