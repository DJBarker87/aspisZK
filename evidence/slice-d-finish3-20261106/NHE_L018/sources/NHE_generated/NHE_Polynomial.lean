import NHE_HornerPort
set_option autoImplicit false
namespace NHE_Polynomial
open Aeneas Aeneas.Std Result AspisR1 LPi_FieldValues

def indices : List Usize := [6#usize,5#usize,4#usize,3#usize,2#usize,1#usize,0#usize]
def zero : NE := ⟨⟨⟨0#u32,0#u32⟩,⟨0#u32,0#u32⟩⟩,⟨⟨0#u32,0#u32⟩,⟨0#u32,0#u32⟩⟩⟩
/-- Transcription of the frozen reverse fold, preserving its ZERO multiply. -/
def source (bytes : Slice U8) (x : NE) : Result NE := NHE_HornerPort.go bytes x indices zero

theorem zero_canonical : canonE zero := by
 repeat' constructor <;> decide

theorem indices_small : ∀ i∈indices,i.val<64 := by
 intro i hi
 simp only [indices,List.mem_cons,List.not_mem_nil,or_false] at hi
 rcases hi with rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide

theorem cohort (bytes : Slice U8) (x : NE) (hx : canonE x) :
 FIo_FieldBridge.map FIo_Install.fromE (source bytes x)=
 FIn_Polynomial.polynomial bytes (FIo_Install.fromE x) :=
 NHE_HornerPort.adopted bytes x zero indices hx zero_canonical indices_small

/-- The cell's extracted add reference is tied to the SAME native product and coefficient. -/
theorem cell (a x coefficient : NE) (ha : canonE a) (hx : canonE x) (hc : canonE coefficient) :
 ∃ product out,
 FIo_Native.aspis_core.field.wide_exact.WideExact.mul a x=ok product ∧ canonE product ∧
 ew product=mulE (ew a) (ew x) ∧
 NGW_HelperRef.polynomial_step_ref (NGW_PolynomialAdd.words product) (NGW_PolynomialAdd.words coefficient)=ok (NGW_PolynomialAdd.words out) ∧
 NGW_Horner.step a x coefficient=ok out ∧ canonE out ∧
 FIn_Primitives.add (FIo_Install.fromE product) (FIo_Install.fromE coefficient)=ok (FIo_Install.fromE out) := by
 obtain ⟨product,out,hp,cp,vp,ref,run,co,_⟩ := NGW_Horner.cell a x coefficient ha hx hc
 have addRun : FIo_Native.aspis_core.field.wide_exact.WideExact.add product coefficient=ok out := by
  simpa only [NGW_Horner.step,hp,bind_tc_ok] using run
 have port := NGW_CurrentAddPort.adopted product coefficient cp hc
 rw [addRun] at port
 exact ⟨product,out,hp,cp,vp,ref,run,co,port.symm⟩

#print axioms zero_canonical
#print axioms indices_small
#print axioms cohort
#print axioms cell
end NHE_Polynomial
