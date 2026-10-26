import RPz7_F3U_AccountEvent
set_option autoImplicit false
namespace AspisR1.F3X_Trace
open FS FS2 FS2.Duplex AspisV8PairedCommitment
open AspisV8R19.MemoizedProgramLaw

variable {I A : Type} [DecidableEq I]

def after (T : Table I A) : List (I × A) → Table I A
  | [] => T
  | (a,f)::tail => after (put T a f) tail

theorem hits_append (bad : I → Table I A → A → Prop)
    (T : Table I A) (left right : List (I × A)) :
    hitsBad bad T (left++right) ↔ hitsBad bad T left ∨ hitsBad bad (after T left) right := by
  induction left generalizing T with
  | nil => simp only [List.nil_append,hitsBad,after,false_or]
  | cons head tail ih =>
    rcases head with ⟨a,f⟩
    simp only [List.cons_append,hitsBad,after,ih,or_assoc]

theorem put_cached (T : Table I A) (a : I) (f : A) (cached : T a=some f) : put T a f=T := by
  funext b
  by_cases same : b=a
  · subst b; simp only [put,ite_true,cached]
  · simp only [put,if_neg same]

theorem after_read (H : I → A) (T : Table I A) (tr : List (I × A))
    (consistent : ∀ q∈tr,q.2=H q.1) (a : I) (read : Read tr a) :
    after T tr a=some (H a) := by
  induction tr generalizing T with
  | nil => simp only [Read,List.map_nil,List.not_mem_nil] at read
  | cons head tail ih =>
    rcases head with ⟨b,f⟩
    have value := consistent (b,f) (List.mem_cons_self)
    have rest : ∀ q∈tail,q.2=H q.1 := fun q h=>consistent q (List.mem_cons_of_mem _ h)
    by_cases again : Read tail a
    · exact ih _ rest again
    · have same : a=b := by
        exact (List.mem_cons.mp read).resolve_right again
      subst b
      have unchanged : ∀ (S : Table I A) (xs : List (I × A)), ¬Read xs a → after S xs a=S a := by
        intro S xs
        induction xs generalizing S with
        | nil => intro _;rfl
        | cons x xs ih =>
          rcases x with ⟨b,g⟩
          intro absent
          have ne : a≠b := fun eq=>absent (by simp only [Read,List.map_cons,List.mem_cons];exact Or.inl eq)
          have absent' : ¬Read xs a := fun h=>absent (by simp only [Read,List.map_cons,List.mem_cons];exact Or.inr h)
          rw [after,ih _ absent']
          simp only [put,if_neg ne]
      rw [after,unchanged _ _ again]
      simp only [put,ite_true]
      exact congrArg some value

theorem reused (bad : I → Table I A → A → Prop) (T : Table I A)
    (replay tail : List (I × A)) (cached : ∀ q∈replay,T q.1=some q.2) :
    hitsBad bad T (replay++tail) ↔ hitsBad bad T tail := by
  induction replay with
  | nil => rfl
  | cons head rest ih =>
    rcases head with ⟨a,f⟩
    have value := cached (a,f) (List.mem_cons_self)
    rw [List.cons_append,hitsBad,put_cached T a f value]
    have restCached : ∀ q∈rest,T q.1=some q.2 := fun q h=>cached q (List.mem_cons_of_mem _ h)
    simp only [value,Option.some_ne_none,false_and,false_or,ih restCached]

theorem erase_reused (bad : I → Table I A → A → Prop) (H : I → A)
    (source replay tail : List (I × A))
    (sourceConsistent : ∀ q∈source,q.2=H q.1)
    (replayConsistent : ∀ q∈replay,q.2=H q.1)
    (included : ∀ a,Read replay a → Read source a) :
    hitsBad bad emptyTable (source++replay++tail) ↔ hitsBad bad emptyTable (source++tail) := by
  have cached : ∀ q∈replay,after emptyTable source q.1=some q.2 := by
    intro q member
    rw [replayConsistent q member]
    exact after_read H _ source sourceConsistent q.1 (included _ (List.mem_map.mpr ⟨q,member,rfl⟩))
  rw [List.append_assoc,hits_append bad emptyTable source (replay++tail),
    reused bad _ replay tail cached,hits_append bad emptyTable source tail]

#print axioms hits_append
#print axioms put_cached
#print axioms after_read
#print axioms reused
#print axioms erase_reused
end AspisR1.F3X_Trace
