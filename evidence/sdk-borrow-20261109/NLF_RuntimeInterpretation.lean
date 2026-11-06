import NLF_Admission
import NLF_ParentModel
set_option autoImplicit false
namespace NLF_RuntimeInterpretation
open AspisR1 NLF_RefCell NLF_SdkModel NLF_ParentModel

def byteList {F : Type} (h : S2Trust.Heap F) (i : Nat) : List UInt8 :=
  List.ofFn (fun j : Fin (h.payload i).descriptor.length => (h.payload i).contents j.val)

def install {F : Type} (h : S2Trust.Heap F) (records : Nat → Account) (money : Nat → Nat) : Parent :=
  ⟨NLF_Admission.initial h records (byteList h) money,0,[]⟩

theorem install_invariant {F : Type} (h : S2Trust.Heap F) (records : Nat → Account)
    (money : Nat → Nat) : Invariant (install h records money) := by
  refine ⟨?_,?_,?_⟩
  · intro i; simp [install,NLF_Admission.initial,Valid]
  · intro i t ht; simp [install,NLF_Admission.initial,HasToken] at ht
  · intro i j t hi; simp [install,NLF_Admission.initial,HasToken] at hi

theorem bytes_length {F : Type} (h : S2Trust.Heap F) (i : Nat) :
    (byteList h i).length = (h.payload i).descriptor.length := by simp [byteList]

theorem bytes_coordinate {F : Type} (h : S2Trust.Heap F) (i : Nat)
    (j : Fin (h.payload i).descriptor.length) :
    (byteList h i)[j.val]'(by simpa [bytes_length] using j.isLt) = (h.payload i).contents j.val := by
  simp [byteList]

theorem install_cells {F : Type} (h : S2Trust.Heap F) (records : Nat → Account)
    (money : Nat → Nat) (a : Nat) :
    ((install h records money).state.accounts a).data = (h.accounts a).1 ∧
    ((install h records money).state.accounts a).lamports = (h.accounts a).2 ∧
    ((install h records money).state.accounts a).key = (records a).key := by
  exact ⟨rfl,rfl,rfl⟩

theorem data_lamports_separate {F : Type} (h : S2Trust.Heap F) (keys : Nat → List UInt8)
    (n a : Nat) (runtime : AdapterRw.RuntimeEntrypointAdmission h keys n) (ha : a<n) :
    (h.accounts a).1 ≠ (h.accounts a).2 :=
  (runtime.valid.2.2.2 a (runtime.liveAccount a ha)).1

#print axioms install_invariant
#print axioms bytes_length
#print axioms bytes_coordinate
#print axioms install_cells
#print axioms data_lamports_separate
end NLF_RuntimeInterpretation
