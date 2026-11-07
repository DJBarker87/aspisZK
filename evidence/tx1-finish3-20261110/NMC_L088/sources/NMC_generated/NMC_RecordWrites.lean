import NMC_RecordOrigins
set_option autoImplicit false
noncomputable section
namespace AspisR1.NMC_Records
open Aeneas Aeneas.Std Result AspisR1PublicPreparation NLC_Finish
theorem record25a {H : Type} (s after : NLC_Finish.State H) (atSite : s.next=.record25a)
 (head : (PreparedHashCode.run (NLC_Finish.step s)).2=ok (.inr after)) :
 Origin after 25#u8 after.locals.record25 := by
 have model : NLC_Finish.step s=NMC_Records.step s 25#u8 .decode25 (fun value=>{s.locals with record25:=some value}) := by
  simp only [NLC_Finish.step,atSite,NMC_Records.step]
  rfl
 rw [model] at head
 exact written s after 25#u8 .decode25 (fun value=>{s.locals with record25:=some value})
  (fun locals=>locals.record25) (fun _=>rfl) head
#print axioms record25a
theorem record25b {H : Type} (s after : NLC_Finish.State H) (atSite : s.next=.record25b)
 (head : (PreparedHashCode.run (NLC_Finish.step s)).2=ok (.inr after)) :
 Origin after 25#u8 after.locals.record25 := by
 have model : NLC_Finish.step s=NMC_Records.step s 25#u8 .circle0 (fun value=>{s.locals with record25:=some value}) := by
  simp only [NLC_Finish.step,atSite,NMC_Records.step]
  rfl
 rw [model] at head
 exact written s after 25#u8 .circle0 (fun value=>{s.locals with record25:=some value})
  (fun locals=>locals.record25) (fun _=>rfl) head
#print axioms record25b
theorem record26a {H : Type} (s after : NLC_Finish.State H) (atSite : s.next=.record26a)
 (head : (PreparedHashCode.run (NLC_Finish.step s)).2=ok (.inr after)) :
 Origin after 26#u8 after.locals.record26 := by
 have model : NLC_Finish.step s=NMC_Records.step s 26#u8 .decode26 (fun value=>{s.locals with record26:=some value}) := by
  simp only [NLC_Finish.step,atSite,NMC_Records.step]
  rfl
 rw [model] at head
 exact written s after 26#u8 .decode26 (fun value=>{s.locals with record26:=some value})
  (fun locals=>locals.record26) (fun _=>rfl) head
#print axioms record26a
theorem record26b {H : Type} (s after : NLC_Finish.State H) (atSite : s.next=.record26b)
 (head : (PreparedHashCode.run (NLC_Finish.step s)).2=ok (.inr after)) :
 Origin after 26#u8 after.locals.record26 := by
 have model : NLC_Finish.step s=NMC_Records.step s 26#u8 .circle1 (fun value=>{s.locals with record26:=some value}) := by
  simp only [NLC_Finish.step,atSite,NMC_Records.step]
  rfl
 rw [model] at head
 exact written s after 26#u8 .circle1 (fun value=>{s.locals with record26:=some value})
  (fun locals=>locals.record26) (fun _=>rfl) head
#print axioms record26b
end AspisR1.NMC_Records
end
