from pathlib import Path
D=Path(__file__).parent
modules={}
def module(name,imports,header,steps):
 text=''.join('import '+s+'\n' for s in imports)+'set_option autoImplicit false\nnoncomputable section\nnamespace PV_DIAG9\nopen Aeneas Aeneas.Std Result\n'+header+'\n'
 chunks=[]
 for name,decl in steps:
  text+=decl+'\n#print axioms '+name+'\n';chunks.append(text+'end PV_DIAG9\n')
 modules['PV_DIAG9_'+name if False else current]=chunks
current='PV_DIAG9_Result'
module(current,['Aeneas'],'',[
('ok_excludes_panic','''theorem ok_excludes_panic {A : Type} {r : Result A} {a : A}
 (h : r=.ok a) : r ≠ .fail .panic := by rw [h]; intro e; cases e'''),
('ok_excludes_div','''theorem ok_excludes_div {A : Type} {r : Result A} {a : A}
 (h : r=.ok a) : r ≠ .div := by rw [h]; intro e; cases e'''),
('ok_excludes_failure','''theorem ok_excludes_failure {A : Type} {r : Result A} {a : A}
 (h : r=.ok a) (e : Error) : r ≠ .fail e := by rw [h]; intro x; cases x'''),
('terminating_excludes_panic','''theorem terminating_excludes_panic {A : Type} {r : Result A}
 (h : ∃ a, r=.ok a) : r ≠ .fail .panic := by
 obtain ⟨a,ha⟩ := h; exact ok_excludes_panic ha'''),
('rust_error_excludes_panic','''theorem rust_error_excludes_panic {A E : Type} {r : Result (core.result.Result A E)}
 (e : E) (h : r=.ok (.Err e)) : r ≠ .fail .panic := ok_excludes_panic h'''),
('bind_prefix_terminates','''theorem bind_prefix_terminates {A B : Type} (r : Result A) (k : A → Result B)
 {b : B} (h : (r >>= k)=.ok b) : ∃ a, r=.ok a ∧ k a=.ok b := by
 cases r with
 | ok a => exact ⟨a,rfl,h⟩
 | fail e => cases h
 | div => cases h'''),
('bind_prefix_no_panic','''theorem bind_prefix_no_panic {A B : Type} (r : Result A) (k : A → Result B)
 {b : B} (h : (r >>= k)=.ok b) : r ≠ .fail .panic := by
 obtain ⟨a,ha,_⟩ := bind_prefix_terminates r k h
 exact ok_excludes_panic ha'''),
('bind_continuation_no_panic','''theorem bind_continuation_no_panic {A B : Type} (r : Result A) (k : A → Result B)
 {b : B} (h : (r >>= k)=.ok b) : ∃ a, r=.ok a ∧ k a ≠ .fail .panic := by
 obtain ⟨a,ha,hk⟩ := bind_prefix_terminates r k h
 exact ⟨a,ha,ok_excludes_panic hk⟩'''),
('bind_failure_propagates','''theorem bind_failure_propagates {A B : Type} (k : A → Result B) :
 ((.fail .panic : Result A) >>= k) = .fail .panic := rfl'''),
('bind_divergence_propagates','''theorem bind_divergence_propagates {A B : Type} (k : A → Result B) :
 ((.div : Result A) >>= k) = .div := rfl'''),
('allowed_result_no_panic','''theorem allowed_result_no_panic {A : Type} (r : Result A) (allowed : Error → Prop)
 (classification : (∃ a, r=.ok a) ∨ (∃ e, allowed e ∧ r=.fail e))
 (nonpanic : ¬ allowed .panic) : r ≠ .fail .panic := by
 rcases classification with h | ⟨e,he,hr⟩
 · exact terminating_excludes_panic h
 · rw [hr]; intro eq; cases eq; exact nonpanic he'''),
('post_does_not_exclude_panic','''theorem post_does_not_exclude_panic {A : Type} (p : A → Prop) :
 (∀ a, (.fail .panic : Result A)=.ok a → p a) ∧
 ¬ ((.fail .panic : Result A) ≠ .fail .panic) := by
 constructor
 · intro a h; cases h
 · intro h; exact h rfl''')])
import json
(D/'plans.json').write_text(json.dumps(modules,indent=2)+'\n')
for m,cs in modules.items():(D/(m+'.lean')).write_text(cs[-1])
