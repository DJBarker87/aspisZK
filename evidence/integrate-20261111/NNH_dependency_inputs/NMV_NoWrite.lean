import NMV_WindowRoots
set_option autoImplicit false
namespace NMV_NoWrite
open RSL

def Free {A : Type} (m : Spec A) : Prop :=
 ∀ env o, m env o → ∀ c b, Event.write c b ∉ o.events

theorem pure_free {A : Type} (a : A) : Free (Spec.pure a) := by
 intro env o h c b
 subst h
 simp

theorem bind_free {A B : Type} (m : Spec A) (k : A → Spec B)
 (hm : Free m) (hk : ∀ a, Free (k a)) : Free (Spec.bind m k) := by
 intro env o h c b hin
 rcases h with ⟨a,e1,o2,h1,h2,ho⟩ | ⟨e1,h1,ho⟩ | ⟨e1,h1,ho⟩
 · subst ho
   rcases List.mem_append.mp hin with hi | hi
   · exact hm env ⟨.ret a,e1⟩ h1 c b hi
   · exact hk a env o2 h2 c b hi
 · subst ho; exact hm env ⟨.abort,e1⟩ h1 c b hin
 · subst ho; exact hm env ⟨.diverge,e1⟩ h1 c b hin

theorem emit_free (e : Event) (he : ∀ c b, e ≠ Event.write c b) : Free (Spec.emit e) := by
 intro env o h c b
 subst h
 simpa [eq_comm] using he c b

theorem env_free {A : Type} (f : Env → A) : Free (Spec.env f) := pure_free_env
 where pure_free_env : Free (Spec.env f) := by intro env o h c b; subst h; simp

theorem alloc_free : Free Spec.alloc := by
 intro env o h c b
 rcases h with h | h <;> subst h <;> simp

theorem panic_free {A : Type} : Free (Spec.panic : Spec A) := by
 intro env o h c b; subst h; simp

theorem call_free {A B : Type} (dom : A → Prop) (law : A → Spec B) (a : A)
 (h : Free (law a)) : Free (Spec.call dom law a) :=
 fun env o ho => h env o ho.2

theorem rs_bind_free {A B : Type} (m : RS A) (k : A → RS B)
 (hm : Free m) (hk : ∀ a, Free (k a)) : Free (RS.bind m k) := by
 apply bind_free _ _ hm
 intro r
 cases r with
 | error e => exact pure_free _
 | ok a => exact hk a

theorem rs_seq_free {B : Type} (m : RS Unit) (k : RS B)
 (hm : Free m) (hk : Free k) : Free (RS.seq m k) := rs_bind_free _ _ hm (fun _ => hk)

theorem check_free (bad : Bool) (e : ProgramError) : Free (RS.check bad e) := by
 cases bad <;> exact pure_free _

theorem ofExcept_free {A : Type} (r : Except ProgramError A) : Free (RS.ofExcept r) := pure_free _

theorem ofOption_free {A : Type} (r : Option A) (e : ProgramError) : Free (RS.ofOption r e) := by
 cases r <;> exact pure_free _

theorem lift_free {A : Type} (m : Spec A) (hm : Free m) : Free (RS.lift m) :=
 bind_free _ _ hm (fun _ => pure_free _)

theorem index_free {A : Type} (as : List A) (i : Nat) : Free (RS.index as i) := by
 unfold RS.index
 split
 · exact pure_free _
 · exact lift_free _ panic_free

/-- These are separate CLOSED child effect obligations, not caller inputs.
Arbitrary PoolLib fields can emit account writes, so none is inferred from a
verifier weak law. They must be installed from their CLOSED packets. -/
structure PoolLaws (L : PoolLib) : Prop where
 scan : ∀ b, Free (L.scanProof b)
 reconstruct : ∀ q a b, Free (L.reconstruct q a b)
 encode : ∀ s, Free (L.encodeStatement s)
 emit : ∀ s, Free (L.emitResult s)

#print axioms pure_free
#print axioms bind_free
#print axioms emit_free
#print axioms env_free
#print axioms alloc_free
#print axioms panic_free
#print axioms call_free
#print axioms rs_bind_free
#print axioms rs_seq_free
#print axioms check_free
#print axioms ofExcept_free
#print axioms ofOption_free
#print axioms lift_free
#print axioms index_free
end NMV_NoWrite
