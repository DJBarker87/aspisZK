import RSL_TX1_094
set_option autoImplicit false
namespace AspisR1.NNG_ReturnedRef094
open RSL

theorem bind_ret {A B : Type} {m : Spec A} {k : A → Spec B} {env : Env}
 {b : B} {ev : List Event} (h : Spec.bind m k env ⟨.ret b,ev⟩) :
 ∃ a e1 e2,m env ⟨.ret a,e1⟩ ∧ k a env ⟨.ret b,e2⟩ := by
 rcases h with ⟨a,e1,o2,hm,hk,eq⟩ | ⟨e,hm,eq⟩ | ⟨e,hm,eq⟩
 · rcases o2 with ⟨out,es⟩
   have same : out=.ret b := (congrArg Obs.exit eq).symm
   cases same
   exact ⟨a,e1,es,hm,hk⟩
 · cases congrArg Obs.exit eq
 · cases congrArg Obs.exit eq
#print axioms bind_ret

theorem bind_ok {E A B : Type} {m : RE E A} {k : A → RE E B} {env : Env}
 {b : B} {ev : List Event} (h : RE.bind m k env ⟨.ret (.ok b),ev⟩) :
 ∃ a e1 e2,m env ⟨.ret (.ok a),e1⟩ ∧ k a env ⟨.ret (.ok b),e2⟩ := by
 obtain ⟨r,e1,e2,hm,hk⟩:=bind_ret h
 cases r with
 | ok a=>exact ⟨a,e1,e2,hm,hk⟩
 | error e=>cases congrArg Obs.exit hk
#print axioms bind_ok

theorem lift_ok {E A : Type} {m : Spec A} {env : Env} {a : A} {ev : List Event}
 (h : (RE.lift m : RE E A) env ⟨.ret (.ok a),ev⟩) :
 ∃ ev',m env ⟨.ret a,ev'⟩ := by
 obtain ⟨x,e1,e2,hm,hk⟩:=bind_ret h
 have same : x=a := Except.ok.inj (Exit.ret.inj (congrArg Obs.exit hk)).symm
 cases same
 exact ⟨e1,hm⟩
#print axioms lift_ok
end AspisR1.NNG_ReturnedRef094
