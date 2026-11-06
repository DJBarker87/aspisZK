import NJG_NativeCuts
set_option autoImplicit false
namespace AspisR1.NJG_RoundsCompose
open Aeneas Aeneas.Std Result AspisR1PublicPreparation NIX_CertificateFrames NJG_NativeCuts

/-- Universal observations of ONE native post recover the entire child Result.
No coordinate chooses a different execution or existential post. -/
theorem complete (s : RoundsPre) (post : RoundOutput) (frame : Nat)
 (cuts : ∀ k z limb,roundsResult s k z limb post frame) : post=s.reply := by
 cases hr:s.reply with
 | Err error=>
   cases hp:post with
   | Err out=>
     have eq:out=error:=by simpa only [roundsResult,hr,hp] using (cuts 0 0 0).2.2
     rw [eq]
   | Ok value=>have bad:False:=by simpa only [roundsResult,hr,hp] using (cuts 0 0 0).2.2
               exact False.elim bad
 | Ok value=>
   rcases value with ⟨r,a,t,n⟩
   cases hp:post with
   | Err error=>have bad:False:=by simpa only [roundsResult,hr,hp] using (cuts 0 0 0).2.2
                exact False.elim bad
   | Ok value=>
     rcases value with ⟨r',a',t',n'⟩
     have each : ∀ k z limb,word r' limb=word r limb ∧
      word (cell a' k) limb=word (cell a k) limb ∧ cell t' z=cell t z ∧ n'=n := by
      intro k z limb
      simpa only [roundsResult,hr,hp] using (cuts k z limb).2.2
     have rr:r'=r:=word_ext _ _ (fun limb=>(each 0 0 limb).1)
     have aa:a'=a:=array_ext _ _ (fun k=>word_ext _ _ (fun limb=>(each k 0 limb).2.1))
     have tt:t'=t:=array_ext _ _ (fun z=>(each 0 z 0).2.2.1)
     have nn:n'=n:=(each 0 0 0).2.2.2
     rw [rr,aa,tt,nn]

/-- The source driver has exactly ten legal call sites; the native counter
precondition is derived rather than supplied at each round. -/
theorem site_domain (r : Fin 10) : r.val<10 ∧ r.val<255 ∧ 15+r.val<27 := by omega

/-- Same child Result transport through a driver continuation, with complete
WireError, outer failure and divergence preserved. No returning/success premise. -/
def bindRust {A B E : Type} (r : Result (core.result.Result A E))
 (next : A→Result (core.result.Result B E)) : Result (core.result.Result B E) := do
 let reply←r
 match reply with | .Ok value=>next value | .Err error=>ok (.Err error)

theorem error_no_suffix {A B E : Type} (error : E) (next other : A→Result (core.result.Result B E)) :
 bindRust (ok (.Err error)) next=bindRust (ok (.Err error)) other := rfl

theorem abort_no_suffix {A B E : Type} (next other : A→Result (core.result.Result B E)) :
 (∀ error,bindRust (.fail error) next=bindRust (.fail error) other) ∧
 bindRust .div next=bindRust .div other := ⟨fun _=>rfl,rfl⟩

#print axioms complete
#print axioms site_domain
#print axioms error_no_suffix
#print axioms abort_no_suffix
end AspisR1.NJG_RoundsCompose
