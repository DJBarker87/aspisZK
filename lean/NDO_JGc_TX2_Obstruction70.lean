import NDO_JGc_TX2_QueryFixture
import NDO_JGc_TX2_InstalledQuery
import NDO_JGc_TX2_M2Leaves
import RPz7_Op5T_Concrete
import RPz8_Rc10_Top
set_option autoImplicit false
namespace AspisR1.JGc_TX2_Obstruction70
open Aeneas Aeneas.Std Result
def folded : Array U8 32#usize := Array.make 32#usize [46#u8,133#u8,21#u8,235#u8,161#u8,197#u8,244#u8,215#u8,120#u8,165#u8,246#u8,0#u8,196#u8,252#u8,96#u8,124#u8,6#u8,55#u8,195#u8,101#u8,6#u8,216#u8,73#u8,254#u8,64#u8,84#u8,104#u8,238#u8,161#u8,99#u8,66#u8,102#u8]
def BatchGoal {Hash : Type} (D : VTop_Stages.aspis_core.digest.Digest32 Hash) (hash : Hash) : Prop :=
  Op5T_Install.stageBatch Port4B_Install.leaves D JFx_NativeBytes.proof JFo_Prepared.value folded 1#usize hash=ok (.Ok ())
#print BatchGoal
#print axioms AspisR1.JGc_TX2_QueryLoop.source
#print axioms AspisR1.JGc_TX2_QueryFixture.on_saved
#print axioms AspisR1.JGc_TX2_QueryFixture.inhabited
#print axioms AspisR1.JGc_TX2_InstalledQuery.source
#print axioms AspisR1.JGc_TX2_M2Roots.hash000
#print axioms AspisR1.JGc_TX2_M2Roots.hash011
#print axioms AspisR1.Rc10_Top.deployed
#check @AspisR1.Rc10_Top.deployed
end AspisR1.JGc_TX2_Obstruction70
