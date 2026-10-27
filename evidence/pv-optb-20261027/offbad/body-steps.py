from step import check,append
m='R1Z/PV_OptB_BodySync';ns='R1Z.PV_OptB_BodySync'
check(m)
append(m,ns,'finish_related','''theorem finish_related {S T : Type} (R : S → T → Prop)
    (left : Result (core.result.Result ProverRwRetryModel.Proof ProverRwFull.verifier.Error × S))
    (right : Result (core.result.Result ProverRwRetryModel.Proof ProverRwFull.verifier.Error × T))
    (same : BodyRelated R left right) : Related R (finish left) (finish right) := by
  cases same with
  | failed e => exact Related.failed e
  | diverged => exact Related.diverged
  | success p q s t h => exact Related.done p q s t h
  | error e s t h =>
    cases e <;> first | exact Related.retry s t h | exact Related.stop _ s t h
''')
append(m,ns,'attempt_finish','''theorem attempt_finish {N L C : Type}
    (account : ProverRwEffectCallback.Account (State N L C))
    (body : Body (State N L C)) (i : Nat) (s next : State N L C)
    (secret : ProverRwRetryModel.Secret)
    (called : entropy account i s = .ok (.Ok secret,next)) :
    attempt account body i s = finish (body secret next) := by
  simp only [attempt,called,bind_tc_ok,Aeneas.Std.uncurry,finish]
''')
append(m,ns,'attempt_entropy_error','''theorem attempt_entropy_error {N L C : Type}
    (account : ProverRwEffectCallback.Account (State N L C))
    (body : Body (State N L C)) (i : Nat) (s next : State N L C)
    (e : ProverRwFull.verifier.Error)
    (called : entropy account i s = .ok (.Err e,next)) :
    attempt account body i s = .ok (.stop (ProverRwRetryModel.error e),next) := by
  simp only [attempt,called,bind_tc_ok,Aeneas.Std.uncurry]
''')
append(m,ns,'attempt_entropy_fail','''theorem attempt_entropy_fail {N L C : Type}
    (account : ProverRwEffectCallback.Account (State N L C))
    (body : Body (State N L C)) (i : Nat) (s : State N L C)
    (e : Aeneas.Std.Error) (called : entropy account i s = .fail e) :
    attempt account body i s = .fail e := by
  simp only [attempt,called,bind_tc_fail]
''')
append(m,ns,'attempt_entropy_div','''theorem attempt_entropy_div {N L C : Type}
    (account : ProverRwEffectCallback.Account (State N L C))
    (body : Body (State N L C)) (i : Nat) (s : State N L C)
    (called : entropy account i s = .div) : attempt account body i s = .div := by
  simp only [attempt,called,bind_tc_div]
''')
append(m,ns,'attempt_related_at_same_state','''theorem attempt_related_at_same_state {N L C : Type}
    (account : ProverRwEffectCallback.Account (State N L C))
    (left right : Body (State N L C)) (i : Nat) (s : State N L C)
    (body_law : ∀ secret next, BodyRelated Eq (left secret next) (right secret next)) :
    Related Eq (attempt account left i s) (attempt account right i s) := by
  cases called : entropy account i s with
  | fail e => rw [attempt_entropy_fail account left i s e called,attempt_entropy_fail account right i s e called]; exact Related.failed e
  | div => rw [attempt_entropy_div account left i s called,attempt_entropy_div account right i s called]; exact Related.diverged
  | ok pair =>
    rcases pair with ⟨status,next⟩
    cases status with
    | Err e =>
      rw [attempt_entropy_error account left i s next e called,attempt_entropy_error account right i s next e called]
      exact Related.stop _ next next rfl
    | Ok secret =>
      rw [attempt_finish account left i s next secret called,attempt_finish account right i s next secret called]
      exact finish_related Eq _ _ (body_law secret next)
''')
