import R1Z.PV_RW_CompressEmission
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RW_CompressIterator
open Aeneas Aeneas.Std Result ControlFlow ProverRwFull ProverRwP6CompressControl
variable [ExternalTypes] [ExternalFuns]

abbrev State := List M × Q × Q

def step (lambda : Q) : State → Result (ControlFlow State Q)
  | ([],out,_) => ok (done out)
  | (value::remaining,out,power) => do
    let (nextOut,nextPower) ← PV_RW_CompressEmission.generated.shipped_step out power value lambda
    ok (cont (remaining,nextOut,nextPower))

def execute (lambda : Q) (remaining : List M) (out power : Q) : Result Q :=
  loop (step lambda) (remaining,out,power)

theorem nil (lambda out power : Q) : execute lambda [] out power = ok out := by
  unfold execute
  rw [ProverRwSuccessPowerTotal.loop_bind]
  rfl

theorem cons (lambda out power : Q) (value : M) (remaining : List M) :
    execute lambda (value::remaining) out power = (do
      let (nextOut,nextPower) ← PV_RW_CompressEmission.generated.shipped_step out power value lambda
      execute lambda remaining nextOut nextPower) := by
  unfold execute
  rw [ProverRwSuccessPowerTotal.loop_bind]
  simp only [step,bind_assoc_eq]
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  rintro ⟨nextOut,nextPower⟩ _
  rfl

theorem fold (lambda : Q) (remaining : List M) (out power : Q) :
    execute lambda remaining out power = PV_CompressList.fold remaining lambda out power := by
  induction remaining generalizing out power with
  | nil => rw [nil,PV_CompressList.nil]
  | cons value remaining ih =>
    rw [cons,PV_CompressList.cons]
    simp only [PV_RW_CompressEmission.generated.shipped_step,bind_assoc_eq,bind_tc_ok]
    repeat' first | apply (Aeneas.Std.bind_eq_iff _ _ _).mpr; intro _ _
    exact ih _ _

def compress (tag : M) (values : Slice M) (lambda : Q) : Result Q := do
  let c ← aspis_core.field.CM31.from_m31 tag
  let out ← aspis_core.field.QM31.from_cm31 c
  execute lambda values.val out lambda

theorem reference (tag : M) (values : Slice M) (lambda : Q) :
    compress tag values lambda = ProverRwP6CompressSource.compress tag values lambda := by
  rw [PV_CompressModel.compress]
  unfold compress
  repeat' first | apply (Aeneas.Std.bind_eq_iff _ _ _).mpr; intro _ _
  exact fold _ _ _ _

theorem arity16 (tag : M) (values : Array M 16#usize) (lambda : Q) :
    compress tag (Array.to_slice values) lambda =
      ProverRwP6CompressSource.compress tag (Array.to_slice values) lambda :=
  reference tag _ lambda
#print axioms nil
#print axioms cons
#print axioms fold
#print axioms reference
#print axioms arity16
end R1Z.PV_RW_CompressIterator
