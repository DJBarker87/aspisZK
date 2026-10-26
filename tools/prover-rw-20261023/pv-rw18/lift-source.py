"""Bind the literal original-source lift emission; no emitted axiom template."""
from pathlib import Path
import hashlib,json,sys
r=Path(__file__).resolve().parents[3];e=r/'evidence/pv-rw18-20261026'
s=(e/'lift-original-Funs.lean.txt').read_text();a=s.index('/-- [aspis_statement::logup::lift]');b=s.index('\nend ProverRw18OriginalLift',a);body=s[a:b]
out='''import R1Z.ProverRw18ContextCompression
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverRw18OriginalLift
open Aeneas Aeneas.Std Result ProverRwFull
section Emitted
variable [ExternalTypes] [ExternalFuns]
'''+body+'''
end Emitted
variable [ExternalTypes]

theorem initial (ops : ExternalFuns) (tag : U32) :
    @logup.lift _ (PV_CurrentScaleInstall.selected ops) tag=
      ok (PV_RW_CompressLiftSelectors.initial tag) := by
  unfold logup.lift
  change (do
    let c ← (PV_CurrentScaleInstall.selected ops).op61 tag
    (PV_CurrentScaleInstall.selected ops).op66 c)=_
  rw [PV_RW_CompressLiftSelectors.complex]
  simp only [bind_tc_ok,PV_RW_CompressLiftSelectors.quartic]
  rfl

def compress (ops : ExternalFuns) (tag : U32) (values : Slice U32)
    (lambda : aspis_core.field.QM31) : Result aspis_core.field.QM31 := do
  let out ← @logup.lift _ (PV_CurrentScaleInstall.selected ops) tag
  let iterator ← SharedSlice.Insts.CoreIterTraitsCollectIntoIteratorSharedIter.into_iter values
  @ProverRw18InlineContext.run _ (PV_CurrentScaleInstall.selected ops) lambda iterator out lambda

theorem context (ops : ExternalFuns) (tag : U32) (values : Slice U32) (lambda : aspis_core.field.QM31) :
    compress ops tag values lambda=
      @ProverRw18ContextCompression.compress _ (PV_CurrentScaleInstall.selected ops) tag values lambda := by
  unfold compress logup.lift ProverRw18ContextCompression.compress
  simp only [bind_assoc_eq]

theorem owned (ops : ExternalFuns) (tag : U32) (values : Slice U32) (lambda : aspis_core.field.QM31) :
    compress ops tag values lambda=PV_RW_CompressClosed.owned tag values lambda :=
  (context ops tag values lambda).trans (ProverRw18ContextCompression.owned ops tag values lambda)

#print axioms initial
#print axioms context
#print axioms owned
end R1Z.ProverRw18OriginalLift
'''
p=r/'docs/research/v8-r0-zk-20261009/lean/R1Z/ProverRw18OriginalLift.lean'
if '--check' in sys.argv:assert p.read_text()==out
else:p.write_text(out)
(e/'original-lift-source-map.json').write_text(json.dumps(dict(emitted_sha256=hashlib.sha256(s.encode()).hexdigest(),literal_body_sha256=hashlib.sha256(body.encode()).hexdigest(),lean_sha256=hashlib.sha256(out.encode()).hexdigest(),changes='Literal original logup::lift body unchanged; imports/namespace/boilerplate adapted to existing Full nominal carriers. External cuts explicitly use existing op61/op66; no axiom template imported and no new max options. Whole original helper source identity remains open.'),indent=2)+'\n')
