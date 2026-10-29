from pathlib import Path
import importlib.util
T=Path(__file__).parent;R=T.resolve().parents[1];L=R/'docs/research/v8-r0-zk-20261009/lean/R1Z'
sp=importlib.util.spec_from_file_location('w',T/'write-module.py');w=importlib.util.module_from_spec(sp);sp.loader.exec_module(w)
imports=['R1Z.PV_RunJoin_CircleNeutralCInv53','R1Z.PV_RunJoin_CircleNeutralCSquare53','R1Z.PV_RunJoin_CircleNeutralRMul53','R1Z.PV_RunJoin_CircleNeutralCSub53','R1Z.PV_RunJoin_CircleNeutralCMul53','R1Z.PV_RunJoin_CircleNeutralCNeg53','R1Z.PV_RunJoin_CircleNeutralZeroResult53']
opaque='attribute [local irreducible] '+ ' '.join(raw+'.field.CM31.'+op for raw in ['PV_RunJoin_CircleRawTower52','PV_RunJoin_CircleR72Raw52'] for op in ['mul','neg','inv','square','sub'])+'\n'
head='open PV_RunJoin_CircleNeutralShape53 PV_RunJoin_CircleNeutralResult53\nabbrev C := U32 × U32\nabbrev Q := C × C\n'+opaque
body=head+'def Valid (x : Option Q) : Prop := ∀ q, x=some q → QC q\n'
for n,raw in [('owned','PV_RunJoin_CircleRawTower52'),('model','PV_RunJoin_CircleR72Raw52')]:
 body+=f'''def {n} (a : Q) (v : C) : Result (Option Q) := do
  let y0 ← {raw}.field.CM31.mul a.1 v
  let neg ← {raw}.field.CM31.neg a.2
  let y1 ← {raw}.field.CM31.mul neg v
  ok (some (y0,y1))
'''
body+='''theorem complete (a : Q) (v : C) (ha : QC a) (hv : CC v) :
    Aligned Valid (owned a v) (model a v) := by
  obtain ⟨y0,h4,h4',hc4⟩ := PV_RunJoin_CircleNeutralCMul53.complete a.1 v ha.1 hv
  obtain ⟨neg,h5,h5',hc5⟩ := PV_RunJoin_CircleNeutralCNeg53.complete a.2 ha.2
  obtain ⟨y1,h6,h6',hc6⟩ := PV_RunJoin_CircleNeutralCMul53.complete neg v hc5 hv
  apply returned _ _ _ (some (y0,y1))
  · simp only [owned,h4,h5,h6,bind_tc_ok]
  · simp only [model,h4',h5',h6',bind_tc_ok]
  · intro q hq
    cases hq
    exact ⟨hc4,hc6⟩
'''
w.write('PV_RunJoin_CircleNeutralQInvTail53',imports,body,['Valid','owned','model','complete'])
body=head
for n,raw in [('owned','PV_RunJoin_CircleRawTower52'),('model','PV_RunJoin_CircleR72Raw52')]:
 body+=f'''def {n} (a : Q) : Result (Option Q) := do
  let s0 ← {raw}.field.CM31.square a.1
  let s1 ← {raw}.field.CM31.square a.2
  let r ← {raw}.field.mul_by_r s1
  let norm ← {raw}.field.CM31.sub s0 r
  let v ← {raw}.field.CM31.inv norm
  PV_RunJoin_CircleNeutralQInvTail53.{n} a v
'''
body+='''theorem complete (a : Q) (ha : QC a) :
    Aligned PV_RunJoin_CircleNeutralQInvTail53.Valid (owned a) (model a) := by
  obtain ⟨s0,h0,h0',hc0⟩ := PV_RunJoin_CircleNeutralCSquare53.complete a.1 ha.1
  obtain ⟨s1,h1,h1',hc1⟩ := PV_RunJoin_CircleNeutralCSquare53.complete a.2 ha.2
  obtain ⟨r,h2,h2',hc2⟩ := PV_RunJoin_CircleNeutralRMul53.complete s1 hc1
  obtain ⟨norm,h3,h3',hc3⟩ := PV_RunJoin_CircleNeutralCSub53.complete s0 r hc0 hc2
  simp only [owned,model,h0,h0',h1,h1',h2,h2',h3,h3',bind_tc_ok]
  exact PV_RunJoin_CircleNeutralResult53.bind (PV_RunJoin_CircleNeutralCInv53.complete norm hc3)
    (fun v hv => PV_RunJoin_CircleNeutralQInvTail53.complete a v ha hv)
'''
w.write('PV_RunJoin_CircleNeutralQInvBody53',['R1Z.PV_RunJoin_CircleNeutralQInvTail53'],body,['owned','model','complete'])
body=head
for n,raw in [('owned','PV_RunJoin_CircleRawTower52'),('model','PV_RunJoin_CircleR72Raw52')]:
 body+=f'''theorem {n} (a : Q) : {raw}.field.QM31.try_inv a = (do
  let z ← {raw}.field.QM31.is_zero a
  if z then ok none else PV_RunJoin_CircleNeutralQInvBody53.{n} a) := by
  unfold {raw}.field.QM31.try_inv PV_RunJoin_CircleNeutralQInvBody53.{n}
    PV_RunJoin_CircleNeutralQInvTail53.{n}
  rfl
'''
w.write('PV_RunJoin_CircleNeutralQInvEquation53',['R1Z.PV_RunJoin_CircleNeutralQInvBody53'],body,['owned','model'])
p=L/'PV_RunJoin_CircleNeutralQInv53.lean'
text="import R1Z.PV_RunJoin_CircleNeutralQInvEquation53\nimport R1Z.PV_RunJoin_CircleNeutralAlignedTransport53\nset_option autoImplicit false\nopen Aeneas Aeneas.Std Result\nnamespace R1Z.PV_RunJoin_CircleNeutralQInv53\nopen PV_RunJoin_CircleNeutralShape53 PV_RunJoin_CircleNeutralResult53\n\ntheorem complete (a : (U32 × U32) × (U32 × U32)) (ha : QC a) :\n    Aligned PV_RunJoin_CircleNeutralQInvTail53.Valid\n      (PV_RunJoin_CircleRawTower52.field.QM31.try_inv a)\n      (PV_RunJoin_CircleR72Raw52.field.QM31.try_inv a) := by\n  obtain ⟨z,hz,hz'⟩ := PV_RunJoin_CircleNeutralZeroResult53.qtotal a\n  apply PV_RunJoin_CircleNeutralAlignedTransport53.transport\n    (PV_RunJoin_CircleNeutralQInvEquation53.owned a)\n    (PV_RunJoin_CircleNeutralQInvEquation53.model a)\n  have hzero : Aligned (fun _ : Bool => True)\n      (PV_RunJoin_CircleRawTower52.field.QM31.is_zero a)\n      (PV_RunJoin_CircleR72Raw52.field.QM31.is_zero a) :=\n    returned _ _ _ z hz hz' True.intro\n  apply PV_RunJoin_CircleNeutralResult53.bind hzero\n  intro b _\n  cases b with\n  | true =>\n    apply returned _ _ _ none rfl rfl\n    intro q hq\n    cases hq\n  | false => exact PV_RunJoin_CircleNeutralQInvBody53.complete a ha\n#print axioms complete\nend R1Z.PV_RunJoin_CircleNeutralQInv53\n"
if __import__('os').environ.get('PV_RUNJOIN53_CHECK'):
 assert p.read_text()==text
 print('matched',p.stem)
else:p.write_text(text)
