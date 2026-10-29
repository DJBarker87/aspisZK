import Init
set_option autoImplicit false
namespace PV_DIAG11

/-! Source control combinators, with primitive call traces retained. This is
not a deployed instance; primitive call bodies and unwinding are not axiomatized.
A halted leaf carries its complete finite prefix, including cleanup effects. -/
inductive Exit (E A : Type) where
 | ok (value : A) | error (value : E) | panic | oom | abort | diverge
 deriving DecidableEq, Repr
structure Run (V E A : Type) where
 events : List V
 exit : Exit E A
 deriving Repr
def ret {V E A : Type} (a : A) : Run V E A := ⟨[],.ok a⟩
def pre {V E A : Type} (xs : List V) (r : Run V E A) : Run V E A := ⟨xs++r.events,r.exit⟩
def seq {V E A B : Type} (r : Run V E A) (f : A → Run V E B) : Run V E B :=
 match r.exit with
 | .ok a => pre r.events (f a)
 | .error e => ⟨r.events,.error e⟩
 | .panic => ⟨r.events,.panic⟩
 | .oom => ⟨r.events,.oom⟩
 | .abort => ⟨r.events,.abort⟩
 | .diverge => ⟨r.events,.diverge⟩
def mapError {V E F A : Type} (f : E → F) (r : Run V E A) : Run V F A :=
 ⟨r.events,match r.exit with
 | .ok a => .ok a | .error e => .error (f e) | .panic => .panic
 | .oom => .oom | .abort => .abort | .diverge => .diverge⟩

theorem pre_empty {V E A : Type} (r : Run V E A) : pre [] r=r := by cases r; simp only [pre,List.nil_append]
#print axioms pre_empty
theorem pre_assoc {V E A : Type} (xs ys : List V) (r : Run V E A) : pre xs (pre ys r)=pre (xs++ys) r := by cases r; simp only [pre,List.append_assoc]
#print axioms pre_assoc
theorem seq_ok {V E A B : Type} (xs : List V) (a : A) (f : A → Run V E B) : seq ⟨xs,.ok a⟩ f=pre xs (f a) := rfl
#print axioms seq_ok
theorem seq_error {V E A B : Type} (xs : List V) (e : E) (f : A → Run V E B) : seq ⟨xs,.error e⟩ f=⟨xs,.error e⟩ := rfl
#print axioms seq_error
theorem seq_panic {V E A B : Type} (xs : List V) (f : A → Run V E B) : seq ⟨xs,.panic⟩ f=⟨xs,.panic⟩ := rfl
#print axioms seq_panic
theorem seq_oom {V E A B : Type} (xs : List V) (f : A → Run V E B) : seq ⟨xs,.oom⟩ f=⟨xs,.oom⟩ := rfl
#print axioms seq_oom
theorem seq_abort {V E A B : Type} (xs : List V) (f : A → Run V E B) : seq ⟨xs,.abort⟩ f=⟨xs,.abort⟩ := rfl
#print axioms seq_abort
theorem seq_diverge {V E A B : Type} (xs : List V) (f : A → Run V E B) : seq ⟨xs,.diverge⟩ f=⟨xs,.diverge⟩ := rfl
#print axioms seq_diverge
theorem seq_ret {V E A B : Type} (a : A) (f : A → Run V E B) : seq (ret a) f=f a := by exact pre_empty (f a)
#print axioms seq_ret
theorem seq_prefix {V E A B : Type} (r : Run V E A) (f : A → Run V E B) : ∃ xs, (seq r f).events=r.events++xs := by cases r with | mk es ex => cases ex <;> simp only [seq,pre] <;> first | exact ⟨_,rfl⟩ | exact ⟨[],(List.append_nil _).symm⟩
#print axioms seq_prefix
theorem seq_assoc {V E A B C : Type} (r : Run V E A) (f : A → Run V E B) (g : B → Run V E C) : seq (seq r f) g=seq r (fun a => seq (f a) g) := by
 cases r with
 | mk es ex =>
   cases ex with
   | ok a =>
     cases h : f a with
     | mk fs fx => cases fx <;> simp only [seq,pre,h,List.append_assoc]
   | error e => rfl
   | panic => rfl
   | oom => rfl
   | abort => rfl
   | diverge => rfl
#print axioms seq_assoc
theorem map_error_prefix {V E F A : Type} (f : E → F) (r : Run V E A) : (mapError f r).events=r.events := rfl
#print axioms map_error_prefix
theorem map_error_normal_result {V E F A : Type} (f : E → F) (es : List V) (e : E) : mapError f (⟨es,.error e⟩ : Run V E A)=⟨es,.error (f e)⟩ := rfl
#print axioms map_error_normal_result
end PV_DIAG11
