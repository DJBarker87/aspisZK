import NMB_MetadataBorrow
set_option autoImplicit false
namespace NMB_MetadataScalar
open NLF_RefCell NLF_SdkModel NMB_Metadata
/-- Scalar SDK wrappers retain their error and returned payload value when
all per-account metadata is replaced at fixed handles. -/
theorem scalar (s : State) (r : Nat → Account) (i t : Nat) (f : Payload → Nat) :
 NLF_SdkModel.scalar (install s r) i t f =
 reply r (NLF_SdkModel.scalar s i t f) := by
 unfold NLF_SdkModel.scalar
 rw [NMB_Metadata.wrap]
 cases h : NLF_SdkModel.wrap s i t .shared with
 | mk post out =>
  cases out with
  | error e => rfl
  | ok g =>
   dsimp only [reply]
   rw [NMB_Metadata.release]
   cases hr : NLF_SdkModel.release post g <;> rfl
#print scalar
#print axioms scalar
end NMB_MetadataScalar
