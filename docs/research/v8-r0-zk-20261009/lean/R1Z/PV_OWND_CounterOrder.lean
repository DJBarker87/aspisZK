import R1Z.PV_OWND_CounterBranch
set_option autoImplicit false
namespace R1Z.PV_OWND_CounterOrder
open PV_OWND_EndpointCounter PV_OWN_Link

theorem producer_error (v : Link) (vs : List Link) (p c : Counts) (e : Error)
 (h:bump p v.producer=.error e) : check (v::vs) p c=.error e := by
 simp only [check,h,Except.bind]

theorem consumer_error (v : Link) (vs : List Link) (p c p' : Counts) (e : Error)
 (hp:bump p v.producer=.ok p') (hc:bump c v.consumer=.error e) :
 check (v::vs) p c=.error e := by
 simp only [check,hp,hc,Except.bind]

theorem success (v : Link) (vs : List Link) (p c p' c' : Counts)
 (hp:bump p v.producer=.ok p') (hc:bump c v.consumer=.ok c') :
 check (v::vs) p c=check vs p' c' := by
 simp only [check,hp,hc,Except.bind]
#print axioms producer_error
#print axioms consumer_error
#print axioms success
end R1Z.PV_OWND_CounterOrder
