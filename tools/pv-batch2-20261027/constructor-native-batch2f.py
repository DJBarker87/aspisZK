"""Compose checked constructor and native Box context on the existing weights carrier."""
from pathlib import Path
import sys
L=Path('docs/research/v8-r0-zk-20261009/lean/R1Z')
s='''import R1Z.PV_B2_F_ConstructorEffect
set_option autoImplicit false
noncomputable section
namespace PV_B2_F_ConstructorNative
open Aeneas Aeneas.Std Result PV_B2_F_ConstructorCarrier
abbrev types := PV_B2_F_MaterializeNative.types
abbrev Outcome := PV_B2_F_MaterializeNative.Outcome

def selected (base : ProverRwFull.ExternalTypes) (request : Result Outcome)
    (boxRequest : Result Unit) (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns (types base) :=
  letI : ProverRwFull.ExternalTypes := types base
  {PV_B2_F_MaterializeNative.selected base request ops with op252 := PV_B2_F_ConstructorEffect.copied boxRequest}

def originalDictionary (base : ProverRwFull.ExternalTypes) (request : Result Outcome)
    (boxRequest : Result Unit) (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns (types base) :=
  letI : ProverRwFull.ExternalTypes := types base
  {PV_B2_F_MaterializeNative.originalDictionary base request ops with op252 := PV_B2_F_ConstructorEffect.original boxRequest}

theorem source (base : ProverRwFull.ExternalTypes) (request : Result Outcome)
    (boxRequest : Result Unit) (ops : @ProverRwFull.ExternalFuns (types base))
    (v : NV) (alpha : Array NQ 10#usize) (z : Array NP 2#usize) :
    @ProverRwFull.ExternalFuns.op252 (types base) (selected base request boxRequest ops) v alpha z =
      PV_B2_F_ConstructorEffect.original boxRequest v alpha z :=
  PV_B2_F_ConstructorEffect.complete_result boxRequest v alpha z

theorem value_law (base : ProverRwFull.ExternalTypes) (request : Result Outcome)
    (ops : @ProverRwFull.ExternalFuns (types base))
    (v : NV) (alpha : Array NQ 10#usize) (z : Array NP 2#usize) :
    ∃ w : Weight,
      PV_B2_C_WeightsNative.host_weights.Weights.new (fromVariant v)
        (amap fromQ alpha) (amap fromPoint z) = ok (.Ok w) ∧
      @ProverRwFull.ExternalFuns.op252 (types base) (selected base request (ok ()) ops) v alpha z =
        ok (.Ok (toWeight w)) := PV_B2_F_ConstructorEffect.value_law v alpha z

theorem nonvacuity (base : ProverRwFull.ExternalTypes) (request : Result Outcome)
    (ops : @ProverRwFull.ExternalFuns (types base))
    (v : NV) (alpha : Array NQ 10#usize) (z : Array NP 2#usize) :
    ∃ w, @ProverRwFull.ExternalFuns.op252 (types base) (selected base request (ok ()) ops) v alpha z =
      ok (.Ok w) := by
  obtain ⟨w,_,hw⟩ := value_law base request ops v alpha z
  exact ⟨toWeight w,hw⟩

theorem failure (base : ProverRwFull.ExternalTypes) (request : Result Outcome) (e : Error)
    (ops : @ProverRwFull.ExternalFuns (types base))
    (v : NV) (alpha : Array NQ 10#usize) (z : Array NP 2#usize) :
    @ProverRwFull.ExternalFuns.op252 (types base) (selected base request (fail e) ops) v alpha z = fail e :=
  PV_B2_F_ConstructorEffect.failure e v alpha z

theorem divergence (base : ProverRwFull.ExternalTypes) (request : Result Outcome)
    (ops : @ProverRwFull.ExternalFuns (types base))
    (v : NV) (alpha : Array NQ 10#usize) (z : Array NP 2#usize) :
    @ProverRwFull.ExternalFuns.op252 (types base) (selected base request div ops) v alpha z = div :=
  PV_B2_F_ConstructorEffect.divergence v alpha z

theorem dictionaries (base : ProverRwFull.ExternalTypes) (request : Result Outcome)
    (boxRequest : Result Unit) (ops : @ProverRwFull.ExternalFuns (types base)) :
    selected base request boxRequest ops = originalDictionary base request boxRequest ops := by
  have hc : PV_B2_F_ConstructorEffect.copied boxRequest = PV_B2_F_ConstructorEffect.original boxRequest := by
    funext v alpha z
    exact PV_B2_F_ConstructorEffect.complete_result boxRequest v alpha z
  unfold selected originalDictionary
  rw [PV_B2_F_MaterializeNative.dictionaries,hc]

theorem observations {O : Sort _} (base : ProverRwFull.ExternalTypes)
    (observe : @ProverRwFull.ExternalFuns (types base) → O) (request : Result Outcome)
    (boxRequest : Result Unit) (ops : @ProverRwFull.ExternalFuns (types base)) :
    observe (selected base request boxRequest ops) = observe (originalDictionary base request boxRequest ops) :=
  congrArg observe (dictionaries base request boxRequest ops)
'''
for n in range(262):
 if n in [249,250,251,252]:continue
 s+=f'''theorem preserved_{n} (base : ProverRwFull.ExternalTypes) (request : Result Outcome)
    (boxRequest : Result Unit) (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op{n} (types base) (selected base request boxRequest ops) =
      @ProverRwFull.ExternalFuns.op{n} (types base) ops := PV_B2_F_MaterializeNative.preserved_{n} base request ops
'''
for name in ['source','value_law','nonvacuity','failure','divergence','dictionaries','observations']+[f'preserved_{n}' for n in range(262) if n not in [249,250,251,252]]:s+='#print axioms '+name+'\n'
s+='end PV_B2_F_ConstructorNative\n'
p=L/'PV_B2_F_ConstructorNative.lean'
if '--check' in sys.argv:assert p.read_text()==s
else:p.write_text(s)
