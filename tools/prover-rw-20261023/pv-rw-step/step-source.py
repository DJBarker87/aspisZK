"""Bind the literal emitted step to existing current primitive source meanings."""
from pathlib import Path
import hashlib,json,sys
r=Path(__file__).resolve().parents[3];e=r/'evidence/pv-rw-step-20261026'
s=(e/'compression-step-Funs.lean.txt').read_text();a=s.index('/-- [pv_rw_step::generated::shipped_step]');b=s.index('\nend PV_RW_CompressNative',a);body=s[a:b]
out='''import R1Z.PV_RW_CompressReference
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RW_CompressEmission
open Aeneas Aeneas.Std Result ControlFlow Error ProverRwFull
variable [ExternalTypes] [ExternalFuns]
'''+body+'''
theorem emitted_step (out power : aspis_core.field.QM31)
    (value : aspis_core.field.M31) (lambda : aspis_core.field.QM31) :
    generated.shipped_step out power value lambda =
      PV_RW_CompressStep.shipped lambda value (out,power) := rfl

theorem emitted_fold (lambda : aspis_core.field.QM31)
    (values : List aspis_core.field.M31) (state : aspis_core.field.QM31 × aspis_core.field.QM31) :
    PV_RW_CompressStep.run (fun value state =>
      generated.shipped_step state.1 state.2 value lambda) values state =
      PV_CompressList.stateFold values lambda state := by
  change PV_RW_CompressStep.run (PV_RW_CompressStep.shipped lambda) values state = _
  exact PV_RW_CompressStep.shipped_fold lambda values state
#print axioms emitted_step
#print axioms emitted_fold
end R1Z.PV_RW_CompressEmission
'''
p=r/'docs/research/v8-r0-zk-20261009/lean/R1Z/PV_RW_CompressEmission.lean'
if '--check' in sys.argv:assert p.read_text()==out
else:p.write_text(out)
(e/'compression-emission-source-map.json').write_text(json.dumps(dict(emitted_sha256=hashlib.sha256(s.encode()).hexdigest(),lean_sha256=hashlib.sha256(out.encode()).hexdigest(),changes='Literal emitted step body unchanged. Import/namespace/boilerplate replaced; same Full nominal carriers and externally parameterized primitive methods used by existing owned-source proofs. Added emitted_step/emitted_fold proofs. No native primitive adequacy inferred.'),indent=2)+'\n')
