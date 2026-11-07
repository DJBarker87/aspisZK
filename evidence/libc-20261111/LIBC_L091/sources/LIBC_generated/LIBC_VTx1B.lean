import LIBC_BatchGraph
import LIBC_Geometry
import LIBC_QueryLoop
import LIBC_F6
set_option autoImplicit false
noncomputable section
namespace LIBC_VTx1B
open RSL
abbrev batchMerkle := LIBC_BatchMerkle.child
abbrev geometry := LIBC_Geometry.child
abbrev queryLoop := LIBC_QueryLoop.child
abbrev checkpoint := LIBC_Checkpoint.child
theorem batchMerkle_exact : batchMerkle=LIBC_BatchMerkle.child := rfl
theorem geometry_exact : geometry=LIBC_Geometry.child := rfl
theorem queryLoop_exact : queryLoop=LIBC_QueryLoop.child := rfl
theorem checkpoint_exact : checkpoint=LIBC_Checkpoint.child := rfl
#print axioms batchMerkle_exact
#print axioms geometry_exact
#print axioms queryLoop_exact
#print axioms checkpoint_exact
end LIBC_VTx1B
