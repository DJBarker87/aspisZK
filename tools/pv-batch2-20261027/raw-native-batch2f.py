"""Install complete frozen raw match on the same exact weights carrier."""
from pathlib import Path
import sys
L=Path('docs/research/v8-r0-zk-20261009/lean/R1Z')
s='''import R1Z.PV_B2_F_ResourceFamilies
import R1Z.PV_B2_F_RawGuard
import R1Z.PV_B2_D_RawTotal
set_option autoImplicit false
noncomputable section
namespace PV_B2_F_RawNative
open Aeneas Aeneas.Std Result PV_B2_F_ConstructorCarrier
abbrev types := PV_B2_F_ResourceFamilies.types
abbrev HeapRequest := PV_B2_F_ResourceFamilies.HeapRequest
abbrev BoxRequest := PV_B2_F_ResourceFamilies.BoxRequest
abbrev Q := PV_B2_251c1.aspis_core.field.QM31

def toNativeQ (q : Q) : NQ := ⟨⟨q.c0.a,q.c0.b⟩,⟨q.c1.a,q.c1.b⟩⟩
def fromNativeQ (q : NQ) : Q := ⟨⟨q.c0.a,q.c0.b⟩,⟨q.c1.a,q.c1.b⟩⟩
theorem roundtrip (q : Q) : fromNativeQ (toNativeQ q)=q := by cases q; rfl
theorem roundtrip_native (q : NQ) : toNativeQ (fromNativeQ q)=q := by cases q; rfl

def callback (w : W) (kind j : Usize) : Result NQ :=
  PV_B2_E_OrdinaryOriginal.mapResult toNativeQ (PV_B2_251c1.host_weights.raw_value w kind j)
def originalCallback (w : W) (kind j : Usize) : Result NQ :=
  PV_B2_E_OrdinaryOriginal.mapResult toNativeQ (PV_B2_F_RawGuard.original w kind j)

def selected (base : ProverRwFull.ExternalTypes) (heap : HeapRequest) (box : BoxRequest)
    (ops : @ProverRwFull.ExternalFuns (types base)) : @ProverRwFull.ExternalFuns (types base) :=
  letI : ProverRwFull.ExternalTypes := types base
  {PV_B2_F_ResourceFamilies.selected base heap box ops with op253 := callback}
def originalDictionary (base : ProverRwFull.ExternalTypes) (heap : HeapRequest) (box : BoxRequest)
    (ops : @ProverRwFull.ExternalFuns (types base)) : @ProverRwFull.ExternalFuns (types base) :=
  letI : ProverRwFull.ExternalTypes := types base
  {PV_B2_F_ResourceFamilies.originalDictionary base heap box ops with op253 := originalCallback}

/-- Every weight, kind and Usize index; errors/divergence are not filtered. -/
theorem copy_equal_original (w : W) (kind j : Usize) :
    callback w kind j = originalCallback w kind j := by
  unfold callback originalCallback
  rw [PV_B2_F_RawGuard.source]

theorem source (base : ProverRwFull.ExternalTypes) (heap : HeapRequest) (box : BoxRequest)
    (ops : @ProverRwFull.ExternalFuns (types base)) (w : W) (kind j : Usize) :
    @ProverRwFull.ExternalFuns.op253 (types base) (selected base heap box ops) w kind j =
      originalCallback w kind j := copy_equal_original w kind j

theorem valid_value_law (base : ProverRwFull.ExternalTypes) (heap : HeapRequest) (box : BoxRequest)
    (ops : @ProverRwFull.ExternalFuns (types base)) (w : W) (kind j : Usize)
    (hk : kind.val<7) (hj : j.val<(1024#usize).val) :
    ∃ q, PV_B2_251c1.host_weights.raw_value w kind j = ok q ∧
      @ProverRwFull.ExternalFuns.op253 (types base) (selected base heap box ops) w kind j = ok (toNativeQ q) := by
  obtain ⟨q,hq⟩ := PV_B2_D_RawTotal.source w kind j hk hj
  exact ⟨q,hq,by change PV_B2_E_OrdinaryOriginal.mapResult toNativeQ _ = _;rw [hq];rfl⟩

theorem nonvacuity (base : ProverRwFull.ExternalTypes) (heap : HeapRequest) (box : BoxRequest)
    (ops : @ProverRwFull.ExternalFuns (types base)) (w : W) :
    ∃ q, @ProverRwFull.ExternalFuns.op253 (types base) (selected base heap box ops) w 0#usize 0#usize = ok q := by
  obtain ⟨q,_,hq⟩ := valid_value_law base heap box ops w 0#usize 0#usize (by decide) (by decide)
  exact ⟨toNativeQ q,hq⟩

theorem dictionaries (base : ProverRwFull.ExternalTypes) (heap : HeapRequest) (box : BoxRequest)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    selected base heap box ops = originalDictionary base heap box ops := by
  have hc : callback=originalCallback := by funext w kind j;exact copy_equal_original w kind j
  unfold selected originalDictionary
  rw [PV_B2_F_ResourceFamilies.dictionaries,hc]

theorem observations {O : Sort _} (base : ProverRwFull.ExternalTypes)
    (observe : @ProverRwFull.ExternalFuns (types base) → O) (heap : HeapRequest) (box : BoxRequest)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    observe (selected base heap box ops) = observe (originalDictionary base heap box ops) :=
  congrArg observe (dictionaries base heap box ops)
'''
for n in range(262):
 if n in [249,250,251,252,253]:continue
 s+=f'''theorem preserved_{n} (base : ProverRwFull.ExternalTypes) (heap : HeapRequest) (box : BoxRequest)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op{n} (types base) (selected base heap box ops) =
      @ProverRwFull.ExternalFuns.op{n} (types base) ops := PV_B2_F_ResourceFamilies.preserved_{n} base heap box ops
'''
for name in ['roundtrip','roundtrip_native','copy_equal_original','source','valid_value_law','nonvacuity','dictionaries','observations']+[f'preserved_{n}' for n in range(262) if n not in [249,250,251,252,253]]:s+='#print axioms '+name+'\n'
s+='end PV_B2_F_RawNative\n'
p=L/'PV_B2_F_RawNative.lean'
if '--check' in sys.argv:assert p.read_text()==s
else:p.write_text(s)
