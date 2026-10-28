import R1Z.PV_DL_EncoderPairs
import R1Z.PV_DL_EncoderFold
import R1Z.PV_CBL_ArrayReadValue
open Aeneas Aeneas.Std Result ProverRwFull
namespace R1Z.PV_DL_EncoderZip
set_option autoImplicit false

def entries {E : Type} (q : Array E 1024#usize) (b : Array E 512#usize) :=
  (PV_DL_EncoderPairs.chunks q.val).zip b.val

theorem count {E : Type} (q : Array E 1024#usize) (b : Array E 512#usize) :
    (entries q b).length=512 := by
  simp only [entries,List.length_zip,PV_DL_EncoderPairs.length,q.property,b.property]
  rfl

theorem coordinate {E : Type} [Inhabited E]
    (q : Array E 1024#usize) (b : Array E 512#usize) (j : Nat) (h : j<512) :
    (entries q b)[j]?=some ((q.val[2*j]!,q.val[2*j+1]!),b.val[j]!) := by
  apply List.getElem?_zip_eq_some.mpr
  refine ⟨?_,?_⟩
  · rw [PV_DL_EncoderPairs.coordinate]
    have he : 2*j<q.val.length := by rw [q.property];change 2*j<1024;omega
    have ho : 2*j+1<q.val.length := by rw [q.property];change 2*j+1<1024;omega
    simp only [List.getElem?_eq_getElem he,List.getElem?_eq_getElem ho,
      PV_CBL_PadListFacts.get_bang q.val _ he,PV_CBL_PadListFacts.get_bang q.val _ ho]
    rfl
  · have hb : j<b.val.length := by rw [b.property];exact h
    rw [List.getElem?_eq_getElem hb,PV_CBL_PadListFacts.get_bang b.val _ hb]

def applyEntry {E : Type} (inst : aspis_core.r0.scalar.CodeField E)
    (entry : (E×E)×E) (p0 p1 : E) : Result (E×E) := do
  let an ← inst.mul entry.1.1 entry.2
  let p0 ← inst.add p0 an
  let bn ← inst.mul entry.1.2 entry.2
  let p1 ← inst.add p1 bn
  ok (p0,p1)

theorem step {E : Type} [Inhabited E] (inst : aspis_core.r0.scalar.CodeField E)
    (q : Array E 1024#usize) (b : Array E 512#usize) (j : Usize)
    (p0 p1 : E) (h : j.val<512) :
    PV_DL_EncoderFold.step inst q b j p0 p1=
      applyEntry inst ((q.val[2*j.val]!,q.val[2*j.val+1]!),b.val[j.val]!) p0 p1 := by
  unfold PV_DL_EncoderFold.step applyEntry
  rw [PV_CBL_ArrayReadValue.read q _ (by rw [PV_DL_EncoderRange.even j h];change 2*j.val<1024;omega)]
  rw [PV_CBL_ArrayReadValue.read b j h]
  rw [PV_CBL_ArrayReadValue.read q _ (by rw [PV_DL_EncoderRange.odd j h];change 2*j.val+1<1024;omega)]
  simp only [PV_DL_EncoderRange.even j h,PV_DL_EncoderRange.odd j h,bind_tc_ok]

#print axioms entries
#print axioms count
#print axioms coordinate
#print axioms applyEntry
#print axioms step
end R1Z.PV_DL_EncoderZip
