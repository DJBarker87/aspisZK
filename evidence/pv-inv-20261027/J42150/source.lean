import R1Z.PV_Inv_RawMapRun
set_option autoImplicit false
namespace R1Z.PV_Inv_RawSchedule
open PV_Inv_RawSlots PV_Inv_RawRun PV_Inv_RawMap PV_Inv_RawMapRun
variable {V U W : Type} [Zero W] [DecidableEq W]

def shape {V W : Type} (s : Slots V W) : Slots Unit W := slots (fun _ => ()) s
def inputShape {V W : Type} (es : List (Entry V W)) : List (Entry Unit W) := es.map (entry (fun _ => ()))

theorem run_shape (s : Slots V W) (es : List (Entry V W)) :
    (run s es).map shape = run (shape s) (inputShape es) := (run_map (fun _ => ()) s es).symm

theorem same_weights (s : Slots V W) (t : Slots U W)
    (es : List (Entry V W)) (fs : List (Entry U W))
    (hstart : shape s=shape t) (hinputs : inputShape es=inputShape fs) :
    (run s es).map shape = (run t fs).map shape := by
  rw [run_shape,run_shape,hstart,hinputs]

#print axioms run_shape
#print axioms same_weights
end R1Z.PV_Inv_RawSchedule
