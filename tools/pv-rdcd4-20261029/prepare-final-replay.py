"""Prepare one focused restored-row interface replay and one frozen manifest."""
from pathlib import Path
import json
R=Path(__file__).resolve().parents[2];E=R/'evidence/pv-rdcd4-20261029';L=R/'docs/research/v8-r0-zk-20261009/lean/R1Z'
rows={n:json.load(open(E/f'rows/V{n}.json')) for n in [201,220,237,236,233,197]}
assert all(rows[n]['status']=='RESTORED' for n in [201,220,237])
s='''import R1Z.PV_RDCD4_FinalAudit
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RDCD4_FocusedReplay
open Aeneas Aeneas.Std Result ProverRwFull

theorem v201 {E : Type} (inst : aspis_core.r0.scalar.CodeField E)
    (q : Array E 1024#usize) (p : aspis_core.r0.domain.Point E) :
    PV_RDCD4_V201.value inst q p=PV_CB_OwnedEncoder.owned.encoder inst q p :=
  PV_RDCD4_V201.source_reference inst q p

theorem v220 (poly : Array PV_RDCD4_LazyComponents.Q 28#usize)
    (challenge : PV_RDCD4_LazyComponents.Q) :
    PV_RDCD4_V220.source poly challenge=PV_RDCD4_V220.reference poly challenge :=
  PV_RDCD4_V220.source_reference poly challenge

theorem v237 {T : Type} (core : Result T) :
    (do let v ← PV_DL_DefaultBuffer.model core;ok (PV_DL_WrapLaw.observe v))=
    (do let c ← core;let v ← PV_DL_Wrap.wrap_reference c;ok (PV_DL_WrapLaw.observeReference v)) :=
  PV_RDCD4_V237.complete core

#print axioms v201
#print axioms v220
#print axioms v237
'''
if rows[197]['status']=='RESTORED':s+='''
theorem v197 (bytes : List U8) :
    PV_RDCD4_BytesSource.qm bytes=PV_RDCD4_V197.reference bytes :=
  PV_RDCD4_V197.source_reference bytes
#print axioms v197
'''
s+='end R1Z.PV_RDCD4_FocusedReplay\n';(L/'PV_RDCD4_FocusedReplay.lean').write_text(s)
# This single final target imports the frozen cohort and focused replay.
# It adds no link hypothesis, new endpoint premise or concrete reduction.
names=['v201','v220','v237']+(['v197'] if rows[197]['status']=='RESTORED' else [])
t='import R1Z.PV_RDCD4_FocusedReplay\n'
t+='\n'.join('#check @R1Z.PV_RDCD4_FocusedReplay.'+n for n in names)+'\n'
t+='\n'.join('#print axioms R1Z.PV_RDCD4_FocusedReplay.'+n for n in names)+'\n'
(L/'PV_RDCD4_FrozenManifest.lean').write_text(t)
(E/'final-replay-rows.json').write_text(json.dumps(dict(rows=[n for n,x in rows.items() if x['status']=='RESTORED'],scope='Exact unchanged source/Result interfaces, using named applications. No endpoint/world or meaning premise removed.'),indent=2)+'\n')
print('Prepared focused restored-row interface replay and one frozen manifest.')
