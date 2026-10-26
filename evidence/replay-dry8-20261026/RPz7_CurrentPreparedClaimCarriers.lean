import CurrentPreparedScratchReachability
import CurrentClaimSourceAggregation
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1ClaimPreparedBridge
abbrev PE := AspisR1PublicPreparation.aspis_core.field.WideExact
abbrev CE := AspisR1CurrentPreparedClaim.aspis_core.field.WideExact
abbrev PQ := AspisR1PublicPreparation.aspis_core.field.QM31
abbrev CQ := AspisR1CurrentPreparedClaim.aspis_core.field.QM31

def toClaimQ (q : PQ) : CQ :=
  {c0:={a:=q.c0.a,b:=q.c0.b},c1:={a:=q.c1.a,b:=q.c1.b}}
def fromClaimQ (q : CQ) : PQ :=
  {c0:={a:=q.c0.a,b:=q.c0.b},c1:={a:=q.c1.a,b:=q.c1.b}}
def toClaimE (x : PE) : CE := {c0:=toClaimQ x.c0,c1:=toClaimQ x.c1}
def fromClaimE (x : CE) : PE := {c0:=fromClaimQ x.c0,c1:=fromClaimQ x.c1}

theorem from_to_q (q : PQ) : fromClaimQ (toClaimQ q)=q := by
  cases q with | mk a b => cases a; cases b; rfl
theorem to_from_q (q : CQ) : toClaimQ (fromClaimQ q)=q := by
  cases q with | mk a b => cases a; cases b; rfl
theorem from_to_e (x : PE) : fromClaimE (toClaimE x)=x := by
  cases x with | mk a b => simp only [toClaimE,fromClaimE,from_to_q]
theorem to_from_e (x : CE) : toClaimE (fromClaimE x)=x := by
  cases x with | mk a b => simp only [toClaimE,fromClaimE,to_from_q]

def mapArray {A B : Type} {N : Usize} (f : A → B) (a : Array A N) : Array B N :=
  ⟨a.val.map f,by simpa only [List.length_map] using a.property⟩
theorem mapArray_inverse {A B : Type} {N : Usize} (f : A → B) (g : B → A)
    (h : ∀ a,g (f a)=a) (a : Array A N) : mapArray g (mapArray f a)=a := by
  apply Subtype.ext
  change (a.val.map f).map g=a.val
  rw [List.map_map]
  have hid : g ∘ f=id := by funext x; exact h x
  rw [hid,List.map_id_fun]
  rfl

theorem from_to_array {N : Usize} (a : Array PE N) :
    mapArray fromClaimE (mapArray toClaimE a)=a :=
  mapArray_inverse toClaimE fromClaimE from_to_e a
theorem to_from_array {N : Usize} (a : Array CE N) :
    mapArray toClaimE (mapArray fromClaimE a)=a :=
  mapArray_inverse fromClaimE toClaimE to_from_e a

#print axioms from_to_e
#print axioms to_from_e
#print axioms mapArray_inverse
#print axioms from_to_array
#print axioms to_from_array
end AspisR1ClaimPreparedBridge
