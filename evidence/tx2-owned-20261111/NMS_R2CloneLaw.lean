import NMS_R2N_GeneralGetters
set_option autoImplicit false
namespace NMS_R2CloneLaw
open RSL
/-- The silent allocation remains before its continuation, including when
that continuation returns an error. No post-abort suffix is evaluated. -/
theorem alloc_then {A B : Type} (a : A) (k : A → Spec B) :
 Spec.bind (Spec.bind Spec.alloc (fun _ => Spec.pure a)) k =
 Spec.bind Spec.alloc (fun _ => k a) := by
 funext env observation
 apply propext
 rw [Spec.bind_two _ _ env a (fun o => by
   rw [Spec.bind_two _ _ env () (fun _ => Iff.rfl)]
   rfl)]
 rw [Spec.bind_two _ _ env () (fun _ => Iff.rfl)]

/-- The emitted getter's interpreted std Clone is exactly RS.ofCloned,
for every stored ProgramError, including nonempty BorshIoError Strings. -/
theorem get {A : Type} (stored : Except ProgramError A) :
 NMS_R2N_GeneralGetters.get stored = RS.ofCloned stored := by
 cases stored with
 | ok a => rfl
 | error e =>
   unfold NMS_R2N_GeneralGetters.get RS.ofCloned
   cases e <;> simp only [NMS_R2N_CloneReference.clone, ProgramError.cloneAllocates,
     Bool.false_eq_true, ↓reduceIte, Spec.bind_pure]
   rename_i text
   by_cases empty : text.isEmpty = true
   · simp only [empty, Bool.not_true, Bool.false_eq_true, ↓reduceIte, Spec.bind_pure]
   · have nonempty : text.isEmpty = false := Bool.eq_false_iff.mpr empty
     simp only [nonempty, Bool.not_false, Bool.true_eq, Bool.false_eq_true, ↓reduceIte]
     rw [alloc_then]
     funext env observation
     apply propext
     rw [Spec.bind_two _ _ env () (fun _ => Iff.rfl)]
     exact (RS.alloc_seq_iff _ env observation).symm

theorem data (a : OwnedAccount) : NMS_R2N_GeneralGetters.data a = a.data := get a.bytes

theorem length (a : OwnedAccount) : NMS_R2N_GeneralGetters.length a = a.data_len := get a.length
#print axioms alloc_then
#print axioms get
#print axioms data
#print axioms length
end NMS_R2CloneLaw
