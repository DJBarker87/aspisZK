"""Keep emitted nominal types and prove the explicit Full-carrier transport."""
from pathlib import Path
import hashlib,json,sys
r=Path(__file__).resolve().parents[3];e=r/'evidence/pv-rw18-20261026'
t=(e/'lift-original-Types.lean.txt').read_text();a=t.index('/-- [aspis_core::field::M31]');b=t.index('\nend ProverRw18OriginalLift',a);types=t[a:b]
f=(e/'lift-original-Funs.lean.txt').read_text();a=f.index('/-- [aspis_statement::logup::lift]');b=f.index('\nend ProverRw18OriginalLift',a);body=f[a:b]
out='''import R1Z.ProverRw18OriginalLift
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverRw18LiftTyped
open Aeneas Aeneas.Std Result
'''+types+'''

class Constructors where
  from_m31 : aspis_core.field.M31 → Result aspis_core.field.CM31
  from_cm31 : aspis_core.field.CM31 → Result aspis_core.field.QM31

def aspis_core.field.CM31.from_m31 [Constructors] (value : aspis_core.field.M31) :
    Result aspis_core.field.CM31 := Constructors.from_m31 value

def aspis_core.field.QM31.from_cm31 [Constructors] (value : aspis_core.field.CM31) :
    Result aspis_core.field.QM31 := Constructors.from_cm31 value

section Emitted
variable [Constructors]
'''+body+'''
end Emitted

def toFullC (x : aspis_core.field.CM31) : ProverRwFull.aspis_core.field.CM31 := ⟨x.a,x.b⟩
def fromFullC (x : ProverRwFull.aspis_core.field.CM31) : aspis_core.field.CM31 := ⟨x.a,x.b⟩
def toFullQ (x : aspis_core.field.QM31) : ProverRwFull.aspis_core.field.QM31 :=
  ⟨toFullC x.c0,toFullC x.c1⟩
def fromFullQ (x : ProverRwFull.aspis_core.field.QM31) : aspis_core.field.QM31 :=
  ⟨fromFullC x.c0,fromFullC x.c1⟩

theorem fullC_roundtrip (x : ProverRwFull.aspis_core.field.CM31) : toFullC (fromFullC x)=x := by
  cases x; rfl

theorem fullQ_roundtrip (x : ProverRwFull.aspis_core.field.QM31) : toFullQ (fromFullQ x)=x := by
  rcases x with ⟨⟨a,b⟩,⟨c,d⟩⟩
  rfl

theorem emittedC_roundtrip (x : aspis_core.field.CM31) : fromFullC (toFullC x)=x := by
  cases x; rfl

theorem emittedQ_roundtrip (x : aspis_core.field.QM31) : fromFullQ (toFullQ x)=x := by
  rcases x with ⟨⟨a,b⟩,⟨c,d⟩⟩
  rfl

variable [ProverRwFull.ExternalTypes]
@[reducible] def interpret (ops : ProverRwFull.ExternalFuns) : Constructors where
  from_m31 := fun value => ProverRwDictionaryTower.mapResult fromFullC (ops.op61 value)
  from_cm31 := fun value => ProverRwDictionaryTower.mapResult fromFullQ (ops.op66 (toFullC value))

theorem transport (ops : ProverRwFull.ExternalFuns) (tag : U32) :
    ProverRwDictionaryTower.mapResult toFullQ (@logup.lift (interpret ops) tag)=
      @ProverRw18OriginalLift.logup.lift _ ops tag := by
  change ProverRwDictionaryTower.mapResult toFullQ (do
    let c ← ProverRwDictionaryTower.mapResult fromFullC (ops.op61 tag)
    ProverRwDictionaryTower.mapResult fromFullQ (ops.op66 (toFullC c))) =
      (do let c ← ops.op61 tag; ops.op66 c)
  cases first : ops.op61 tag with
  | fail error => rfl
  | div => rfl
  | ok c =>
    simp only [ProverRwDictionaryTower.mapResult,bind_tc_ok,fullC_roundtrip]
    cases second : ops.op66 c <;> simp only [ProverRwDictionaryTower.mapResult,fullQ_roundtrip]

theorem initial (ops : ProverRwFull.ExternalFuns) (tag : U32) :
    ProverRwDictionaryTower.mapResult toFullQ
      (@logup.lift (interpret (PV_CurrentScaleInstall.selected ops)) tag)=
        ok (PV_RW_CompressLiftSelectors.initial tag) := by
  rw [transport,ProverRw18OriginalLift.initial]

#print axioms fullC_roundtrip
#print axioms fullQ_roundtrip
#print axioms emittedC_roundtrip
#print axioms emittedQ_roundtrip
#print axioms transport
#print axioms initial
end R1Z.ProverRw18LiftTyped
'''
p=r/'docs/research/v8-r0-zk-20261009/lean/R1Z/ProverRw18LiftTyped.lean'
if '--check' in sys.argv:assert p.read_text()==out
else:p.write_text(out)
(e/'original-lift-nominal-map.json').write_text(json.dumps(dict(emitted_types_body_sha256=hashlib.sha256(types.encode()).hexdigest(),emitted_function_body_sha256=hashlib.sha256(body.encode()).hexdigest(),lean_sha256=hashlib.sha256(out.encode()).hexdigest(),scope='Preserves literal emitted type/function bodies. External constructor cuts are parameterized data and explicitly transported to Full op61/op66 with all Result branches. No axiom template, source rewrite or whole-helper source identity.'),indent=2)+'\n')
