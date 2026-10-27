import R1Z.PV_Inv_RawSchedule
set_option autoImplicit false
namespace R1Z.PV_Inv_RawFailure
open PV_Inv_RawSlots PV_Inv_RawRun PV_Inv_RawSchedule
variable {V U W : Type} [Zero W] [DecidableEq W]

theorem failure_iff (s : Slots V W) (t : Slots U W)
    (es : List (Entry V W)) (fs : List (Entry U W))
    (hstart : shape s=shape t) (hinputs : inputShape es=inputShape fs) :
    run s es=none ↔ run t fs=none := by
  have h := same_weights s t es fs hstart hinputs
  cases hr : run s es <;> cases ht : run t fs <;> simp_all

#print axioms failure_iff
end R1Z.PV_Inv_RawFailure
