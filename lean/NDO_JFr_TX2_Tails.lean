import NDO_JFr_TX2_Tails10
import NDO_JFr_TX2_Tails11
import NDO_JFr_TX2_Tails12
import NDO_JFr_TX2_Tails13
import NDO_JFr_TX2_Tails14
import NDO_JFr_TX2_Tails15
import NDO_JFr_TX2_Tails16
import NDO_JFr_TX2_Tails17
import NDO_JFr_TX2_Tails18
import NDO_JFr_TX2_Tails19
import NDO_JFr_TX2_Tails20
import NDO_JFr_TX2_Tails21
set_option autoImplicit false
noncomputable section
namespace AspisR1.JFr_TX2_Tails
open Aeneas Aeneas.Std Result

def start (slot : Fin 4) (kind : Fin 3) : Nat :=
  if kind.val=0 then 120*slot.val+104 else 480+32*slot.val+16*(kind.val-1)
def offset (slot : Fin 4) (kind : Fin 3) : Usize := Usize.ofNat (start slot kind) (by
  have := slot.isLt;have := kind.isLt;unfold start;split <;> scalar_tac)
def stop (slot : Fin 4) (kind : Fin 3) : Usize := Usize.ofNat (start slot kind+16) (by
  have := slot.isLt;have := kind.isLt;unfold start;split <;> scalar_tac)

def position (i : Fin 12) : Fin 22 := ⟨i.val+10,by have:=i.isLt;omega⟩

/-- All144 native QM31 tail reads on the SAME real proof. This asserts no
pairing result, dot-loop return, fold equality or wrapper acceptance. -/
theorem source (i : Fin 12) (slot : Fin 4) (kind : Fin 3) :
    ∃ value, JFr_TX2_TailRead.read (JFr_TX2_Windows.array (position i))
      (offset slot kind) (stop slot kind)=ok value := by
  fin_cases i
  · fin_cases kind
    · fin_cases slot
      · exact ⟨_,JFr_TX2_Tails10.source0_0⟩
      · exact ⟨_,JFr_TX2_Tails10.source0_1⟩
      · exact ⟨_,JFr_TX2_Tails10.source0_2⟩
      · exact ⟨_,JFr_TX2_Tails10.source0_3⟩
    · fin_cases slot
      · exact ⟨_,JFr_TX2_Tails10.source1_0⟩
      · exact ⟨_,JFr_TX2_Tails10.source1_1⟩
      · exact ⟨_,JFr_TX2_Tails10.source1_2⟩
      · exact ⟨_,JFr_TX2_Tails10.source1_3⟩
    · fin_cases slot
      · exact ⟨_,JFr_TX2_Tails10.source2_0⟩
      · exact ⟨_,JFr_TX2_Tails10.source2_1⟩
      · exact ⟨_,JFr_TX2_Tails10.source2_2⟩
      · exact ⟨_,JFr_TX2_Tails10.source2_3⟩
  · fin_cases kind
    · fin_cases slot
      · exact ⟨_,JFr_TX2_Tails11.source0_0⟩
      · exact ⟨_,JFr_TX2_Tails11.source0_1⟩
      · exact ⟨_,JFr_TX2_Tails11.source0_2⟩
      · exact ⟨_,JFr_TX2_Tails11.source0_3⟩
    · fin_cases slot
      · exact ⟨_,JFr_TX2_Tails11.source1_0⟩
      · exact ⟨_,JFr_TX2_Tails11.source1_1⟩
      · exact ⟨_,JFr_TX2_Tails11.source1_2⟩
      · exact ⟨_,JFr_TX2_Tails11.source1_3⟩
    · fin_cases slot
      · exact ⟨_,JFr_TX2_Tails11.source2_0⟩
      · exact ⟨_,JFr_TX2_Tails11.source2_1⟩
      · exact ⟨_,JFr_TX2_Tails11.source2_2⟩
      · exact ⟨_,JFr_TX2_Tails11.source2_3⟩
  · fin_cases kind
    · fin_cases slot
      · exact ⟨_,JFr_TX2_Tails12.source0_0⟩
      · exact ⟨_,JFr_TX2_Tails12.source0_1⟩
      · exact ⟨_,JFr_TX2_Tails12.source0_2⟩
      · exact ⟨_,JFr_TX2_Tails12.source0_3⟩
    · fin_cases slot
      · exact ⟨_,JFr_TX2_Tails12.source1_0⟩
      · exact ⟨_,JFr_TX2_Tails12.source1_1⟩
      · exact ⟨_,JFr_TX2_Tails12.source1_2⟩
      · exact ⟨_,JFr_TX2_Tails12.source1_3⟩
    · fin_cases slot
      · exact ⟨_,JFr_TX2_Tails12.source2_0⟩
      · exact ⟨_,JFr_TX2_Tails12.source2_1⟩
      · exact ⟨_,JFr_TX2_Tails12.source2_2⟩
      · exact ⟨_,JFr_TX2_Tails12.source2_3⟩
  · fin_cases kind
    · fin_cases slot
      · exact ⟨_,JFr_TX2_Tails13.source0_0⟩
      · exact ⟨_,JFr_TX2_Tails13.source0_1⟩
      · exact ⟨_,JFr_TX2_Tails13.source0_2⟩
      · exact ⟨_,JFr_TX2_Tails13.source0_3⟩
    · fin_cases slot
      · exact ⟨_,JFr_TX2_Tails13.source1_0⟩
      · exact ⟨_,JFr_TX2_Tails13.source1_1⟩
      · exact ⟨_,JFr_TX2_Tails13.source1_2⟩
      · exact ⟨_,JFr_TX2_Tails13.source1_3⟩
    · fin_cases slot
      · exact ⟨_,JFr_TX2_Tails13.source2_0⟩
      · exact ⟨_,JFr_TX2_Tails13.source2_1⟩
      · exact ⟨_,JFr_TX2_Tails13.source2_2⟩
      · exact ⟨_,JFr_TX2_Tails13.source2_3⟩
  · fin_cases kind
    · fin_cases slot
      · exact ⟨_,JFr_TX2_Tails14.source0_0⟩
      · exact ⟨_,JFr_TX2_Tails14.source0_1⟩
      · exact ⟨_,JFr_TX2_Tails14.source0_2⟩
      · exact ⟨_,JFr_TX2_Tails14.source0_3⟩
    · fin_cases slot
      · exact ⟨_,JFr_TX2_Tails14.source1_0⟩
      · exact ⟨_,JFr_TX2_Tails14.source1_1⟩
      · exact ⟨_,JFr_TX2_Tails14.source1_2⟩
      · exact ⟨_,JFr_TX2_Tails14.source1_3⟩
    · fin_cases slot
      · exact ⟨_,JFr_TX2_Tails14.source2_0⟩
      · exact ⟨_,JFr_TX2_Tails14.source2_1⟩
      · exact ⟨_,JFr_TX2_Tails14.source2_2⟩
      · exact ⟨_,JFr_TX2_Tails14.source2_3⟩
  · fin_cases kind
    · fin_cases slot
      · exact ⟨_,JFr_TX2_Tails15.source0_0⟩
      · exact ⟨_,JFr_TX2_Tails15.source0_1⟩
      · exact ⟨_,JFr_TX2_Tails15.source0_2⟩
      · exact ⟨_,JFr_TX2_Tails15.source0_3⟩
    · fin_cases slot
      · exact ⟨_,JFr_TX2_Tails15.source1_0⟩
      · exact ⟨_,JFr_TX2_Tails15.source1_1⟩
      · exact ⟨_,JFr_TX2_Tails15.source1_2⟩
      · exact ⟨_,JFr_TX2_Tails15.source1_3⟩
    · fin_cases slot
      · exact ⟨_,JFr_TX2_Tails15.source2_0⟩
      · exact ⟨_,JFr_TX2_Tails15.source2_1⟩
      · exact ⟨_,JFr_TX2_Tails15.source2_2⟩
      · exact ⟨_,JFr_TX2_Tails15.source2_3⟩
  · fin_cases kind
    · fin_cases slot
      · exact ⟨_,JFr_TX2_Tails16.source0_0⟩
      · exact ⟨_,JFr_TX2_Tails16.source0_1⟩
      · exact ⟨_,JFr_TX2_Tails16.source0_2⟩
      · exact ⟨_,JFr_TX2_Tails16.source0_3⟩
    · fin_cases slot
      · exact ⟨_,JFr_TX2_Tails16.source1_0⟩
      · exact ⟨_,JFr_TX2_Tails16.source1_1⟩
      · exact ⟨_,JFr_TX2_Tails16.source1_2⟩
      · exact ⟨_,JFr_TX2_Tails16.source1_3⟩
    · fin_cases slot
      · exact ⟨_,JFr_TX2_Tails16.source2_0⟩
      · exact ⟨_,JFr_TX2_Tails16.source2_1⟩
      · exact ⟨_,JFr_TX2_Tails16.source2_2⟩
      · exact ⟨_,JFr_TX2_Tails16.source2_3⟩
  · fin_cases kind
    · fin_cases slot
      · exact ⟨_,JFr_TX2_Tails17.source0_0⟩
      · exact ⟨_,JFr_TX2_Tails17.source0_1⟩
      · exact ⟨_,JFr_TX2_Tails17.source0_2⟩
      · exact ⟨_,JFr_TX2_Tails17.source0_3⟩
    · fin_cases slot
      · exact ⟨_,JFr_TX2_Tails17.source1_0⟩
      · exact ⟨_,JFr_TX2_Tails17.source1_1⟩
      · exact ⟨_,JFr_TX2_Tails17.source1_2⟩
      · exact ⟨_,JFr_TX2_Tails17.source1_3⟩
    · fin_cases slot
      · exact ⟨_,JFr_TX2_Tails17.source2_0⟩
      · exact ⟨_,JFr_TX2_Tails17.source2_1⟩
      · exact ⟨_,JFr_TX2_Tails17.source2_2⟩
      · exact ⟨_,JFr_TX2_Tails17.source2_3⟩
  · fin_cases kind
    · fin_cases slot
      · exact ⟨_,JFr_TX2_Tails18.source0_0⟩
      · exact ⟨_,JFr_TX2_Tails18.source0_1⟩
      · exact ⟨_,JFr_TX2_Tails18.source0_2⟩
      · exact ⟨_,JFr_TX2_Tails18.source0_3⟩
    · fin_cases slot
      · exact ⟨_,JFr_TX2_Tails18.source1_0⟩
      · exact ⟨_,JFr_TX2_Tails18.source1_1⟩
      · exact ⟨_,JFr_TX2_Tails18.source1_2⟩
      · exact ⟨_,JFr_TX2_Tails18.source1_3⟩
    · fin_cases slot
      · exact ⟨_,JFr_TX2_Tails18.source2_0⟩
      · exact ⟨_,JFr_TX2_Tails18.source2_1⟩
      · exact ⟨_,JFr_TX2_Tails18.source2_2⟩
      · exact ⟨_,JFr_TX2_Tails18.source2_3⟩
  · fin_cases kind
    · fin_cases slot
      · exact ⟨_,JFr_TX2_Tails19.source0_0⟩
      · exact ⟨_,JFr_TX2_Tails19.source0_1⟩
      · exact ⟨_,JFr_TX2_Tails19.source0_2⟩
      · exact ⟨_,JFr_TX2_Tails19.source0_3⟩
    · fin_cases slot
      · exact ⟨_,JFr_TX2_Tails19.source1_0⟩
      · exact ⟨_,JFr_TX2_Tails19.source1_1⟩
      · exact ⟨_,JFr_TX2_Tails19.source1_2⟩
      · exact ⟨_,JFr_TX2_Tails19.source1_3⟩
    · fin_cases slot
      · exact ⟨_,JFr_TX2_Tails19.source2_0⟩
      · exact ⟨_,JFr_TX2_Tails19.source2_1⟩
      · exact ⟨_,JFr_TX2_Tails19.source2_2⟩
      · exact ⟨_,JFr_TX2_Tails19.source2_3⟩
  · fin_cases kind
    · fin_cases slot
      · exact ⟨_,JFr_TX2_Tails20.source0_0⟩
      · exact ⟨_,JFr_TX2_Tails20.source0_1⟩
      · exact ⟨_,JFr_TX2_Tails20.source0_2⟩
      · exact ⟨_,JFr_TX2_Tails20.source0_3⟩
    · fin_cases slot
      · exact ⟨_,JFr_TX2_Tails20.source1_0⟩
      · exact ⟨_,JFr_TX2_Tails20.source1_1⟩
      · exact ⟨_,JFr_TX2_Tails20.source1_2⟩
      · exact ⟨_,JFr_TX2_Tails20.source1_3⟩
    · fin_cases slot
      · exact ⟨_,JFr_TX2_Tails20.source2_0⟩
      · exact ⟨_,JFr_TX2_Tails20.source2_1⟩
      · exact ⟨_,JFr_TX2_Tails20.source2_2⟩
      · exact ⟨_,JFr_TX2_Tails20.source2_3⟩
  · fin_cases kind
    · fin_cases slot
      · exact ⟨_,JFr_TX2_Tails21.source0_0⟩
      · exact ⟨_,JFr_TX2_Tails21.source0_1⟩
      · exact ⟨_,JFr_TX2_Tails21.source0_2⟩
      · exact ⟨_,JFr_TX2_Tails21.source0_3⟩
    · fin_cases slot
      · exact ⟨_,JFr_TX2_Tails21.source1_0⟩
      · exact ⟨_,JFr_TX2_Tails21.source1_1⟩
      · exact ⟨_,JFr_TX2_Tails21.source1_2⟩
      · exact ⟨_,JFr_TX2_Tails21.source1_3⟩
    · fin_cases slot
      · exact ⟨_,JFr_TX2_Tails21.source2_0⟩
      · exact ⟨_,JFr_TX2_Tails21.source2_1⟩
      · exact ⟨_,JFr_TX2_Tails21.source2_2⟩
      · exact ⟨_,JFr_TX2_Tails21.source2_3⟩

#print axioms source
end AspisR1.JFr_TX2_Tails
end
