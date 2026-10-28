"""Do not restrict native resource outcomes to input-independent constants."""
from pathlib import Path
import sys
L=Path('docs/research/v8-r0-zk-20261009/lean/R1Z')
s='''import R1Z.PV_B2_F_252Closure
import R1Z.PV_B2_F_ConstructorCarrierLaws
set_option autoImplicit false
noncomputable section
namespace PV_B2_F_ResourceFamilies
open Aeneas Aeneas.Std Result PV_B2_F_ConstructorCarrier
abbrev types := PV_B2_F_MaterializeNative.types
abbrev Native := PV_B2_F_MaterializeNative.Native
abbrev Outcome := PV_B2_F_MaterializeNative.Outcome
/-- Arbitrary input-dependent resource contexts; no witness-independence premise. -/
abbrev HeapRequest := W → Native → Result Outcome
abbrev BoxRequest := NV → Array NQ 10#usize → Array NP 2#usize → Result Unit

def heapCallback (heap : HeapRequest) (w : W) (kappa : Native) :=
  PV_B2_F_MaterializeNative.callback (heap w kappa) w kappa
def heapOriginal (heap : HeapRequest) (w : W) (kappa : Native) :=
  PV_B2_E_OrdinaryOriginal.mapResult PV_B2_F_MaterializeNative.mapRust
    (PV_B2_F_MaterializeRequest.original (heap w kappa) w
      (PV_B2_F_MaterializeNative.fromNative kappa))
def boxCallback (box : BoxRequest) (v : NV) (alpha : Array NQ 10#usize) (z : Array NP 2#usize) :=
  PV_B2_F_ConstructorEffect.copied (box v alpha z) v alpha z
def boxOriginal (box : BoxRequest) (v : NV) (alpha : Array NQ 10#usize) (z : Array NP 2#usize) :=
  PV_B2_F_ConstructorEffect.original (box v alpha z) v alpha z

def selected (base : ProverRwFull.ExternalTypes) (heap : HeapRequest) (box : BoxRequest)
    (ops : @ProverRwFull.ExternalFuns (types base)) : @ProverRwFull.ExternalFuns (types base) :=
  letI : ProverRwFull.ExternalTypes := types base
  {@PV_B2_E_GammaOriginal.selected (types base) ops with
    op251 := heapCallback heap,op252 := boxCallback box}
def originalDictionary (base : ProverRwFull.ExternalTypes) (heap : HeapRequest) (box : BoxRequest)
    (ops : @ProverRwFull.ExternalFuns (types base)) : @ProverRwFull.ExternalFuns (types base) :=
  letI : ProverRwFull.ExternalTypes := types base
  {@PV_B2_E_GammaOriginal.originalDictionary (types base) ops with
    op251 := heapOriginal heap,op252 := boxOriginal box}

theorem heap_source (heap : HeapRequest) (w : W) (kappa : Native) :
    heapCallback heap w kappa = heapOriginal heap w kappa := by
  unfold heapCallback PV_B2_F_MaterializeNative.callback heapOriginal
  rw [PV_B2_F_MaterializeRequest.complete_result]

theorem box_source (box : BoxRequest) (v : NV) (alpha : Array NQ 10#usize) (z : Array NP 2#usize) :
    boxCallback box v alpha z = boxOriginal box v alpha z :=
  PV_B2_F_ConstructorEffect.complete_result _ v alpha z

theorem selected_heap (base : ProverRwFull.ExternalTypes) (heap : HeapRequest) (box : BoxRequest)
    (ops : @ProverRwFull.ExternalFuns (types base)) (w : W) (kappa : Native) :
    @ProverRwFull.ExternalFuns.op251 (types base) (selected base heap box ops) w kappa =
      heapOriginal heap w kappa := heap_source heap w kappa

theorem selected_box (base : ProverRwFull.ExternalTypes) (heap : HeapRequest) (box : BoxRequest)
    (ops : @ProverRwFull.ExternalFuns (types base)) (v : NV) (alpha : Array NQ 10#usize) (z : Array NP 2#usize) :
    @ProverRwFull.ExternalFuns.op252 (types base) (selected base heap box ops) v alpha z =
      boxOriginal box v alpha z := box_source box v alpha z

theorem dictionaries (base : ProverRwFull.ExternalTypes) (heap : HeapRequest) (box : BoxRequest)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    selected base heap box ops = originalDictionary base heap box ops := by
  have hh : heapCallback heap = heapOriginal heap := by funext w kappa; exact heap_source heap w kappa
  have hb : boxCallback box = boxOriginal box := by funext v alpha z; exact box_source box v alpha z
  unfold selected originalDictionary
  rw [@PV_B2_E_GammaOriginal.dictionaries (types base) ops,hh,hb]

theorem observations {O : Sort _} (base : ProverRwFull.ExternalTypes)
    (observe : @ProverRwFull.ExternalFuns (types base) → O) (heap : HeapRequest) (box : BoxRequest)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    observe (selected base heap box ops) = observe (originalDictionary base heap box ops) :=
  congrArg observe (dictionaries base heap box ops)

theorem heap_nonvacuity (base : ProverRwFull.ExternalTypes)
    (ops : @ProverRwFull.ExternalFuns (types base)) (w : W) (kappa : Native) :
    ∃ out, @ProverRwFull.ExternalFuns.op251 (types base)
      (selected base (fun _ _ => ok .supplied) (fun _ _ _ => ok ()) ops) w kappa = ok (.Ok out) :=
  PV_B2_F_MaterializeNative.nonvacuity base ops w kappa

theorem box_nonvacuity (base : ProverRwFull.ExternalTypes)
    (ops : @ProverRwFull.ExternalFuns (types base)) (v : NV) (alpha : Array NQ 10#usize) (z : Array NP 2#usize) :
    ∃ out, @ProverRwFull.ExternalFuns.op252 (types base)
      (selected base (fun _ _ => ok .supplied) (fun _ _ _ => ok ()) ops) v alpha z = ok (.Ok out) := by
  obtain ⟨w,_,hw⟩ := PV_B2_F_ConstructorEffect.value_law v alpha z
  exact ⟨toWeight w,hw⟩
'''
for n in range(262):
 if n in [249,250,251,252]:continue
 s+=f'''theorem preserved_{n} (base : ProverRwFull.ExternalTypes) (heap : HeapRequest) (box : BoxRequest)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op{n} (types base) (selected base heap box ops) =
      @ProverRwFull.ExternalFuns.op{n} (types base) ops := @PV_B2_E_GammaOriginal.preserved_{n} (types base) ops
'''
for name in ['heap_source','box_source','selected_heap','selected_box','dictionaries','observations','heap_nonvacuity','box_nonvacuity']+[f'preserved_{n}' for n in range(262) if n not in [249,250,251,252]]:s+='#print axioms '+name+'\n'
s+='end PV_B2_F_ResourceFamilies\n'
p=L/'PV_B2_F_ResourceFamilies.lean'
if '--check' in sys.argv:assert p.read_text()==s
else:p.write_text(s)
