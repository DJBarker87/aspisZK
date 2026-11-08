import pathlib
L=pathlib.Path('lean')
(L/'PV_LIB_SliceNativeGraph.lean').write_text('''import PV_LIB_Observation
import PV_W5_NativeLeaves
set_option autoImplicit false
noncomputable section
namespace PV_LIB_SliceNativeGraph
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine PV_EVHB_OWNER
open PV_W5_LeafBoundary
/-- Literal output function in the CLOSED slice leaf provider's Post. -/
def internalModel (C : Carrier OWNER Data) (e : Entry) (callee : Data)
    (H : PV_W5_NativeFrame.Backend) (w : OWNER) (prior : List PV_RJ4IDB.NativeEvent) :=
  deliver C e callee (PV_STX2_Source7QUniformResourceHandler.lift H
    (.child callee e.store.nextActivation e.arguments) w) prior

def model (C : Carrier OWNER Data) (e : Entry) (callee : Data)
    (H : PV_W5_NativeFrame.Backend) (w : OWNER) (prior : List PV_RJ4IDB.NativeEvent)
    (stack : List Config) :=
  PV_LIB.observe (⟨internalModel C e callee H w prior,stack⟩ :
    PV_THR2_IntrinsicState.State OWNER PV_RJ4IDB.NativeEvent)
#print axioms internalModel
#print axioms model
end PV_LIB_SliceNativeGraph
''')
for group,ns in {'SliceAllocNative':['f62','f46','f36','f37','f38'],
                 'SliceLoopNative':['f20','f16','f17','f18','f10'],
                 'SliceBuiltinNative':['arrayRepeat','arrayToSliceMut','arrayToSliceShared','indexMut']}.items():
 s='''import PV_LIB_SliceNativeGraph
set_option autoImplicit false
noncomputable section
namespace PV_LIB_'''+group+'''
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine PV_EVHB_OWNER
open PV_W5_LeafBoundary
'''
 for n in ns:
  s+=f'''
def model_{n} (C : Carrier OWNER Data) (e : Entry)
    (H : PV_W5_NativeFrame.Backend) (w : OWNER) (prior : List PV_RJ4IDB.NativeEvent) (stack : List Config) :=
  PV_LIB_SliceNativeGraph.model C e PV_W5_NativeLeaves.callee_{n} H w prior stack

def law_{n} (C : Carrier OWNER Data) (e : Entry)
    (H : PV_W5_NativeFrame.Backend) (w : OWNER) (prior : List PV_RJ4IDB.NativeEvent) (stack : List Config)
    (out : PV_LIB.MachineObservation OWNER PV_RJ4IDB.NativeEvent) : Prop :=
  out = model_{n} C e H w prior stack

theorem certified_{n} (C : Carrier OWNER Data) (e : Entry)
    (H : PV_W5_NativeFrame.Backend) (w : OWNER) (prior : List PV_RJ4IDB.NativeEvent) (stack : List Config)
    (pre : Pre e w) :
    law_{n} C e H w prior stack (PV_LIB_SliceNativeGraph.model C e PV_W5_NativeLeaves.callee_{n} H w prior stack) ∧
    Post C e PV_W5_NativeLeaves.callee_{n} H w prior :=
  ⟨rfl,PV_W5_NativeLeaves.{n} C e H w prior pre⟩
#print axioms certified_{n}
'''
 s+='end PV_LIB_'+group+'\n';(L/('PV_LIB_'+group+'.lean')).write_text(s)
