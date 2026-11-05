import NIM_NHY_COMBINED_IMPORT
import NHL_Tx1Model
set_option autoImplicit false
noncomputable section
namespace NIS_Tx1PortProbe
/-- Interface preflight only. This is not a native bridge or an adoption. -/
def install (adapter : AdapterRw.Ops) (base : AspisR1CurrentCaller.Ops)
    (first : ∀ H : Type, AspisR1.NHL_EmittedTx1.Prepare H) : AdapterRw.Ops :=
  {adapter with op10 := fun {H} D pub public_bytes proof k hash obs =>
    AspisR1.NHL_EmittedTx1.tx1 base (first H) D pub public_bytes proof k hash obs}
#print axioms install
end NIS_Tx1PortProbe
