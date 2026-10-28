import R1Z.PV_CompressModel
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_CompressTransport
open Aeneas Aeneas.Std Result ProverRwFull ProverRwP6CompressControl
variable [ExternalTypes]
-- Only primitive agreements are hypotheses. The complete fold equation is proved.
theorem stateFold (left right : ExternalFuns)
    (scale : left.op70=right.op70) (add : left.op67=right.op67) (mul : left.op69=right.op69)
    (values : List M) (lambda : Q) (state : Q × Q) :
    @PV_CompressList.stateFold _ left values lambda state =
      @PV_CompressList.stateFold _ right values lambda state := by
  induction values generalizing state with
  | nil => rfl
  | cons m ms ih =>
    rcases state with ⟨out,power⟩
    change (do
      let q ← left.op70 power m
      let out1 ← left.op67 out q
      let power1 ← left.op69 power lambda
      @PV_CompressList.stateFold _ left ms lambda (out1,power1)) = _
    rw [scale,add,mul]
    repeat' first | apply (Aeneas.Std.bind_eq_iff _ _ _).mpr; intro _ _
    exact ih _

theorem fold (left right : ExternalFuns)
    (scale : left.op70=right.op70) (add : left.op67=right.op67) (mul : left.op69=right.op69)
    (values : List M) (lambda out power : Q) :
    @PV_CompressList.fold _ left values lambda out power =
      @PV_CompressList.fold _ right values lambda out power := by
  unfold PV_CompressList.fold
  rw [stateFold left right scale add mul]
#print axioms stateFold
#print axioms fold
end R1Z.PV_CompressTransport
