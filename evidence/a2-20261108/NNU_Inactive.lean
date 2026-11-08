import NNU_InactiveStructure
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNU_Inactive
open Aeneas Aeneas.Std Result NNU_InactiveStructure
/-- Push the coordinate port through the symbolic decoder binds. No byte
slice is evaluated and no array read is reduced. -/
theorem source (bs : Slice U8) :
 Port1_LibrarySource.decode bs=NJC_ClosedCalls.inactive bs := by
 change Port1_LibrarySource.decode bs=post (Option.map FIo_Install.fromE)
   (FIo_Native.aspis_core.field.wide_exact.WideExact.from_le_bytes bs)
 unfold FIo_Native.aspis_core.field.wide_exact.WideExact.from_le_bytes
 simp only [post_bind,post_if,post_ok,Option.map]
 simp only [←limbs]
 unfold Port1_LibrarySource.decode FIo_Native.aspis_core.field.wide_exact.WideExact.BYTE_LEN
 rfl

theorem returned : NNH_Tx2OpenSlots.inactive := source
#print axioms source
#print axioms returned
end AspisR1.NNU_Inactive
end
