import NGL_EntryRouting
set_option autoImplicit false
noncomputable section
namespace AspisR1.NIS_EntryPrefixes
open Aeneas Aeneas.Std Result

theorem rejected_head (data : Slice U8) (tag : U8)
    (head : data.val.head?=some tag) (notFirst : tag≠3#u8) (notRequest : tag≠65#u8) :
    Hiq_ReleaseRoute.route data=.reject := by
  cases route : Hiq_ReleaseRoute.route data with
  | reject => rfl
  | first =>
    rcases NGL_EntryRouting.first_domain data route with ten | eleven
    · have same : data.val.head?=some (3#u8) := by rw [ten]; rfl
      exact False.elim (notFirst (Option.some.inj (head.symm.trans same)))
    · have same : data.val.head?=some (3#u8) := by rw [eleven]; rfl
      exact False.elim (notFirst (Option.some.inj (head.symm.trans same)))
  | second =>
    have pref := NGL_EntryRouting.second_domain data route
    have sameHead : (data.val.take 4).head?=data.val.head? := by cases data.val <;> rfl
    have same := congrArg List.head? pref
    rw [sameHead] at same
    exact False.elim (notRequest (Option.some.inj (head.symm.trans same)))

theorem lifecycle4 (data : Slice U8) (head : data.val.head?=some (4#u8)) :
    Hiq_ReleaseRoute.route data=.reject := rejected_head data _ head (by decide) (by decide)
theorem lifecycle5 (data : Slice U8) (head : data.val.head?=some (5#u8)) :
    Hiq_ReleaseRoute.route data=.reject := rejected_head data _ head (by decide) (by decide)
theorem lifecycle6 (data : Slice U8) (head : data.val.head?=some (6#u8)) :
    Hiq_ReleaseRoute.route data=.reject := rejected_head data _ head (by decide) (by decide)

theorem other_reject (data : Slice U8)
    (notTen : data.val≠[3#u8,10#u8]) (notEleven : data.val≠[3#u8,11#u8])
    (notRequest : data.val.take 4≠[65#u8,83#u8,81#u8,56#u8]) :
    Hiq_ReleaseRoute.route data=.reject := by
  cases route : Hiq_ReleaseRoute.route data with
  | reject => rfl
  | first =>
    rcases NGL_EntryRouting.first_domain data route with ten | eleven
    · exact False.elim (notTen ten)
    · exact False.elim (notEleven eleven)
  | second => exact False.elim (notRequest (NGL_EntryRouting.second_domain data route))

/-- Full returning reply, state and ordered effects of the selected child are
forwarded. No successful child outcome or parent-output equation is assumed. -/
theorem first_forward {Account State Event : Type}
    (children : NGL_EntryRouting.Children Account State Event)
    (id : NGL_EntryRouting.Key) (accounts : Slice Account) (data : Slice U8) (state : State)
    (selected : Hiq_ReleaseRoute.route data=.first) :
    NGL_EntryRouting.run children id accounts data state =
      (children.first id accounts data state,[.first id accounts data]) := by
  simp only [NGL_EntryRouting.run,selected]

theorem second_forward {Account State Event : Type}
    (children : NGL_EntryRouting.Children Account State Event)
    (id : NGL_EntryRouting.Key) (accounts : Slice Account) (data : Slice U8) (state : State)
    (selected : Hiq_ReleaseRoute.route data=.second) :
    NGL_EntryRouting.run children id accounts data state =
      (children.second id accounts data state,[.second id accounts data]) := by
  simp only [NGL_EntryRouting.run,selected]

theorem abort_prefix {Account State Event : Type}
    (children : NGL_EntryRouting.Children Account State Event)
    (id : NGL_EntryRouting.Key) (accounts : Slice Account) (data : Slice U8) (state : State)
    (rejected : Hiq_ReleaseRoute.route data=.reject) :
    NGL_EntryRouting.run children id accounts data state =
      (⟨ok (.Err .InvalidInstructionData),state,[]⟩,[]) :=
  NGL_EntryRouting.rejected_frame children id accounts data state rejected

#print axioms rejected_head
#print axioms lifecycle4
#print axioms lifecycle5
#print axioms lifecycle6
#print axioms other_reject
#print axioms first_forward
#print axioms second_forward
#print axioms abort_prefix
end AspisR1.NIS_EntryPrefixes
