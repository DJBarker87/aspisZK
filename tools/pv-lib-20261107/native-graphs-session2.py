"""Generate graph adapters from the CLOSED native providers' deterministic proof functions."""
import pathlib
L=pathlib.Path('lean')
(L/'PV_LIB_NativeGraph.lean').write_text('''import PV_LIB_Observation
import PV_W1_ArgumentEffects
set_option autoImplicit false
noncomputable section
namespace PV_LIB_NativeGraph
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_EVHB_OwnerMachine
open PV_W1_LeafBoundary PV_W1_OwnerNativeFrame
/-- This is the exact let-bound output of ArgumentEffects.Post/full_reply.
The explicit effects family is an environment input, not a chosen identity. -/
def internalModel {E : Type} (C : Carrier OWNER Data) (d : Entry)
    (H : Backend E) (w : OWNER) (events : List E) (changes : Address → Option Data) :=
  deliver C (PV_W1_ArgumentEffects.afterEffects C d w changes)
    (PV_THR2_OwnUniformResourceHandler.lift H
      (.child d.callee d.store.nextActivation d.arguments) w) events

def model {E : Type} (C : Carrier OWNER Data) (d : Entry)
    (H : Backend E) (w : OWNER) (events : List E) (changes : Address → Option Data) :=
  PV_LIB.observe (internalModel C d H w events changes)

theorem certified {E : Type} (C : Carrier OWNER Data) (d : Entry)
    (H : Backend E) (w : OWNER) (events : List E) (changes : Address → Option Data)
    (pre : PV_W1_ClosedLeaves.Pre d w) :
    model C d H w events changes = PV_LIB.observe (internalModel C d H w events changes) ∧
      PV_W1_ArgumentEffects.Post C d H w events changes :=
  ⟨rfl,PV_W1_ArgumentEffects.full_reply C d H w events changes pre⟩
#print axioms certified
end PV_LIB_NativeGraph
''')
groups={'SpawnNative':[213,295,452,453,454,455,456,457,459],
        'ScopeNative':[269,271,14,165,168,7,8],
        'TlsNative':[410,319,11,122,127,128,129,130],
        'RootNative':[3,4,171,268]}
for group,ns in groups.items():
 s='''import PV_LIB_NativeGraph
import PV_W1_NativeLeaves
set_option autoImplicit false
noncomputable section
namespace PV_LIB_'''+group+'''
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_EVHB_OwnerMachine
open PV_W1_LeafBoundary PV_W1_OwnerNativeFrame
'''
 for n in ns:
  s+=f'''
def model{n} {{E : Type}} (C : Carrier OWNER Data) (e : Entry)
    (H : Backend E) (w : OWNER) (args : List Data) (events : List E)
    (changes : Address → Option Data) :=
  PV_LIB_NativeGraph.model C (PV_W1_NativeLeaves.entry{n} e args) H w events changes

def law{n} {{E : Type}} (C : Carrier OWNER Data) (e : Entry)
    (H : Backend E) (w : OWNER) (args : List Data) (events : List E)
    (changes : Address → Option Data) (out : PV_LIB.MachineObservation OWNER E) : Prop :=
  out = model{n} C e H w args events changes

theorem certified{n} {{E : Type}} (C : Carrier OWNER Data) (e : Entry)
    (H : Backend E) (w : OWNER) (args : List Data) (events : List E)
    (changes : Address → Option Data) (pre : PV_W1_NativeLeaves.Pre e w) :
    law{n} C e H w args events changes
      (PV_LIB.observe (PV_LIB_NativeGraph.internalModel C
        (PV_W1_NativeLeaves.entry{n} e args) H w events changes)) ∧
      PV_W1_NativeLeaves.Post{n} C e H w args events changes :=
  ⟨rfl,PV_W1_NativeLeaves.f{n} C e H w args events changes pre⟩
#print axioms certified{n}
'''
 s+='end PV_LIB_'+group+'\n';(L/('PV_LIB_'+group+'.lean')).write_text(s)
