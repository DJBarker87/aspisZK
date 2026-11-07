import LIB_VLib
import LIBC_S1Validated
set_option autoImplicit false
noncomputable section
namespace LIB_S1
open RSL
/-- Actual module24 instance; Public is definitionally the canonical carrier. -/
def library : TX1_345.S1Lib LIB_VLib.library := LIBC_S1.library LIB_VLib.library rfl
theorem public_type : LIB_VLib.library.Public = LIB_VCarriers.Public := rfl
theorem library_exact : library = LIBC_S1.library LIB_VLib.library rfl := rfl
theorem decoder (b : Bytes) : library.decodeStatement b = LIBC_S1.decode b := rfl
theorem validator (s : library.Statement) : library.validateStatement s = LIBC_S1.valid s := rfl
theorem encoder (s : library.Statement) : library.encodeCandidate s = LIBC_S1.encode s := rfl
theorem semantic (s : library.Statement) : library.semanticPublic s =
 AspisR1.NJB_SemanticPublic.value (NMT_345Prep.toT7 s) := LIBC_S1.semantic_value s
theorem validated_public (s : library.Statement) (good : library.validateStatement s=true) :
 LIB_VLib.library.publicDom (library.semanticPublic s) := LIBC_S1Validated.validated s good
/-- F4 uses the SAME before-first-Box probe, including subsequent error paths. -/
theorem allocation (b : Aeneas.Std.Slice Aeneas.Std.U8) :
 library.decodeReachesAlloc (b.val.map NMT_345.byte)=true ↔
 NMT_R2_Reach.full LIBC_FirstBox.beforeBox b=.div := LIBC_S1Sources.allocation b
#print axioms public_type
#print axioms library_exact
#print axioms decoder
#print axioms validator
#print axioms encoder
#print axioms semantic
#print axioms validated_public
#print axioms allocation
end LIB_S1
