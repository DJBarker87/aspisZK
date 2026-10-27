import JFx_SourcePorts
import Rc3_Install
set_option autoImplicit false
noncomputable section
namespace AspisR1.JFx_PortCompatibility
open Aeneas Aeneas.Std Result
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep

/-- CPH and Rc3 can share the exact selected dictionary, not just equal
acceptance decisions. No accepted execution or frozen3 join follows here. -/
theorem same_dictionary {F C : Type} (c : DrvC_Installation.Configuration F C)
    (indexError : C) (H : Bytes → State) :
    JFx_SourcePorts.configuration c indexError H =
      Rc3_Install.configuration
        (CPP_Install.configuration (JFx_SourcePorts.select c indexError H)) (.Ok ()) := by
  unfold JFx_SourcePorts.configuration
  rw [CPH_Install.rc2]
  exact ((Rc3_Install.exact_scope _ _).mpr rfl).symm

#print axioms same_dictionary
end AspisR1.JFx_PortCompatibility
end
