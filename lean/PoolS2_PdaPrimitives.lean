import PoolS2_PdaSource
set_option autoImplicit false
noncomputable section
namespace AspisR1.PoolS2_PdaPrimitives
open Aeneas Aeneas.Std Result PoolS2_PdaSource

theorem accepted (ops : Ops) (seeds : Slice (Slice U8)) (program key : Key)
    (h : registry.stored_bump_address_matches ops seeds program key = ok true) :
    ops.create seeds program = ok (.Ok key) := by
  unfold registry.stored_bump_address_matches at h
  cases call : ops.create seeds program with
  | fail e => simp [call] at h
  | div => simp [call] at h
  | ok result =>
    cases result with
    | Err e => simp [call] at h
    | Ok address =>
      have eq : address = key := Hist_Authority.keyEq_true address key (by simpa [call] using h)
      simpa [eq] using call

theorem ready (ops : Ops) (seeds : Slice (Slice U8)) (program key : Key)
    (call : ops.create seeds program = ok (.Ok key)) :
    registry.stored_bump_address_matches ops seeds program key = ok true := by
  classical
  simp [registry.stored_bump_address_matches,call,Hist_Authority.keyEq]

theorem rejected (ops : Ops) (seeds : Slice (Slice U8)) (program key : Key) (e : PdaError)
    (call : ops.create seeds program = ok (.Err e)) :
    registry.stored_bump_address_matches ops seeds program key = ok false := by
  simp [registry.stored_bump_address_matches,call]

theorem failed (ops : Ops) (seeds : Slice (Slice U8)) (program key : Key) (e : Error)
    (call : ops.create seeds program = .fail e) :
    registry.stored_bump_address_matches ops seeds program key = .fail e := by
  simp [registry.stored_bump_address_matches,call]

theorem diverged (ops : Ops) (seeds : Slice (Slice U8)) (program key : Key)
    (call : ops.create seeds program = .div) :
    registry.stored_bump_address_matches ops seeds program key = .div := by
  simp [registry.stored_bump_address_matches,call]

#print axioms accepted
#print axioms ready
#print axioms rejected
#print axioms failed
#print axioms diverged
end AspisR1.PoolS2_PdaPrimitives
end
