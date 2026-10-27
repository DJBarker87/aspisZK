import RPz7_WAdm_SourceWriter
import RPz7_Tx1Q_PrefixInstall
set_option autoImplicit false
noncomputable section
open Aeneas Aeneas.Std Result
namespace AspisR1.WAdm_Install
open Tx1Q_Carriers

/-- Concrete append-content body for the writer slot. Its native-source
qualification is the bounded Port3 certificate; it is not an all-input Rust
or ELF interpretation. -/
def writer {H : Type} (D : AspisR1CurrentCaller.aspis_core.digest.Digest32 H)
    (p : C.P) (a : C.A) (proof pub : Slice U8) (hash : H) : Result (alloc.vec.Vec U8) :=
  WAdm_SourceWriter.writer (Tx1Q_Install.digest D) (prepared p) (accumulator a) proof pub hash

def base {CoreError : Type} (ops : AspisR1CurrentCaller.Ops) (reserved : Bool)
    (query : Port3_NativeQueryBody.Ops) (geo : Port3_NativeGeometryBody.Ops CoreError) :=
  {Tx1Q_PrefixInstall.install ops reserved query geo with op16 := writer}

theorem other_slots {CoreError : Type} (ops : AspisR1CurrentCaller.Ops) (reserved : Bool)
    (query : Port3_NativeQueryBody.Ops) (geo : Port3_NativeGeometryBody.Ops CoreError) :
    {base ops reserved query geo with op16 := Tx1Q_Install.writer} =
      Tx1Q_PrefixInstall.install ops reserved query geo := rfl

#print axioms other_slots
end AspisR1.WAdm_Install
end
