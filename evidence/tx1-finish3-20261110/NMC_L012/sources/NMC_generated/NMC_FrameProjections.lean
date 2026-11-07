import NMC_ValueFrame
set_option autoImplicit false
noncomputable section
namespace AspisR1.NMC_Frame
open Aeneas Aeneas.Std Result AspisR1PublicPreparation
/-- ALL projection indices are universally quantified. No chosen cell or
pre-filled output is equated with the complete parent frame. -/
def Same (a b : Value) : Prop := ∀ tag i j,field a tag i j=field b tag i j
theorem running (a b : Value) (same : Same a b) : a.running=b.running := by
 apply NLU.word_ext
 intro j
 apply UScalar.eq_of_val_eq
 simpa [field] using same ⟨0,by decide⟩ ⟨0,by decide⟩ j
theorem terminal (a b : Value) (same : Same a b) : a.terminal=b.terminal := by
 apply NLU.word_ext
 intro j
 apply UScalar.eq_of_val_eq
 simpa [field] using same ⟨3,by decide⟩ ⟨0,by decide⟩ j
theorem mask (a b : Value) (same : Same a b) : a.mask=b.mask := by
 apply NLU.word_ext
 intro j
 apply UScalar.eq_of_val_eq
 simpa [field] using same ⟨4,by decide⟩ ⟨0,by decide⟩ j
theorem z0_x (a b : Value) (same : Same a b) : a.z0.x=b.z0.x := by
 apply NLU.word_ext
 intro j
 apply UScalar.eq_of_val_eq
 simpa [field] using same ⟨8,by decide⟩ ⟨0,by decide⟩ j
theorem z0_y (a b : Value) (same : Same a b) : a.z0.y=b.z0.y := by
 apply NLU.word_ext
 intro j
 apply UScalar.eq_of_val_eq
 simpa [field] using same ⟨9,by decide⟩ ⟨0,by decide⟩ j
theorem z1_x (a b : Value) (same : Same a b) : a.z1.x=b.z1.x := by
 apply NLU.word_ext
 intro j
 apply UScalar.eq_of_val_eq
 simpa [field] using same ⟨10,by decide⟩ ⟨0,by decide⟩ j
theorem z1_y (a b : Value) (same : Same a b) : a.z1.y=b.z1.y := by
 apply NLU.word_ext
 intro j
 apply UScalar.eq_of_val_eq
 simpa [field] using same ⟨11,by decide⟩ ⟨0,by decide⟩ j
theorem challenges_lambda (a b : Value) (same : Same a b) : a.challenges.lambda=b.challenges.lambda := by
 apply NLU.word_ext
 intro j
 apply UScalar.eq_of_val_eq
 simpa [field] using same ⟨17,by decide⟩ ⟨0,by decide⟩ j
theorem challenges_chi (a b : Value) (same : Same a b) : a.challenges.chi=b.challenges.chi := by
 apply NLU.word_ext
 intro j
 apply UScalar.eq_of_val_eq
 simpa [field] using same ⟨18,by decide⟩ ⟨0,by decide⟩ j
theorem challenges_theta (a b : Value) (same : Same a b) : a.challenges.theta=b.challenges.theta := by
 apply NLU.word_ext
 intro j
 apply UScalar.eq_of_val_eq
 simpa [field] using same ⟨19,by decide⟩ ⟨0,by decide⟩ j
theorem challenges_mu (a b : Value) (same : Same a b) : a.challenges.mu=b.challenges.mu := by
 apply NLU.word_ext
 intro j
 apply UScalar.eq_of_val_eq
 simpa [field] using same ⟨21,by decide⟩ ⟨0,by decide⟩ j
theorem challenges_eta (a b : Value) (same : Same a b) : a.challenges.eta=b.challenges.eta := by
 apply NLU.word_ext
 intro j
 apply UScalar.eq_of_val_eq
 simpa [field] using same ⟨22,by decide⟩ ⟨0,by decide⟩ j
theorem alpha (a b : Value) (same : Same a b) : a.alpha=b.alpha := by
 apply NLU.cells_ext
 intro i hi
 apply NLU.word_ext
 intro j
 apply UScalar.eq_of_val_eq
 have hr : i%10=i := Nat.mod_eq_of_lt hi
 simpa [field,hr] using same ⟨1,by decide⟩ ⟨i,by omega⟩ j
theorem extra (a b : Value) (same : Same a b) : a.extra=b.extra := by
 apply NLU.cells_ext
 intro i hi
 apply NLU.word_ext
 intro j
 apply UScalar.eq_of_val_eq
 have hr : i%29=i := Nat.mod_eq_of_lt hi
 simpa [field,hr] using same ⟨5,by decide⟩ ⟨i,by omega⟩ j
theorem before (a b : Value) (same : Same a b) : a.before=b.before := by
 apply NLU.cells_ext
 intro i hi
 apply NLU.word_ext
 intro j
 apply UScalar.eq_of_val_eq
 have hr : i%29=i := Nat.mod_eq_of_lt hi
 simpa [field,hr] using same ⟨6,by decide⟩ ⟨i,by omega⟩ j
theorem challenges_zc (a b : Value) (same : Same a b) : a.challenges.zc=b.challenges.zc := by
 apply NLU.cells_ext
 intro i hi
 apply NLU.word_ext
 intro j
 apply UScalar.eq_of_val_eq
 have hr : i%10=i := Nat.mod_eq_of_lt hi
 simpa [field,hr] using same ⟨20,by decide⟩ ⟨i,by omega⟩ j
theorem state (a b : Value) (same : Same a b) : a.state=b.state := by
 apply NLU.cells_ext
 intro i hi
 apply UScalar.eq_of_val_eq
 have hr : i%32=i := Nat.mod_eq_of_lt hi
 simpa [field,hr] using same ⟨7,by decide⟩ ⟨i,by omega⟩ ⟨0,by decide⟩
theorem rest (a b : Value) (same : Same a b) : a.rest=b.rest := by
 apply NLU.cells_ext
 intro i hi
 apply UScalar.eq_of_val_eq
 have hr : i%32=i := Nat.mod_eq_of_lt hi
 simpa [field,hr] using same ⟨12,by decide⟩ ⟨i,by omega⟩ ⟨0,by decide⟩
theorem transcript_state (a b : Value) (same : Same a b) : a.transcript.state=b.transcript.state := by
 apply NLU.cells_ext
 intro i hi
 apply UScalar.eq_of_val_eq
 have hr : i%32=i := Nat.mod_eq_of_lt hi
 simpa [field,hr] using same ⟨15,by decide⟩ ⟨i,by omega⟩ ⟨0,by decide⟩
theorem claims_value (a b : Value) (same : Same a b) : a.claims.value=b.claims.value := by
 apply NLU.cells_ext
 intro row hrow
 apply NLU.cells_ext
 intro col hcol
 apply NLU.word_ext
 intro j
 apply UScalar.eq_of_val_eq
 have hdiv : (row*29+col)/29=row := by omega
 have hmod : (row*29+col)%29=col := by omega
 simpa [field,hdiv,hmod] using same ⟨2,by decide⟩ ⟨row*29+col,by omega⟩ j
theorem claims_identity (a b : Value) (same : Same a b) : a.claims.identity=b.claims.identity := by
 simpa [field] using same ⟨14,by decide⟩ ⟨0,by decide⟩ ⟨0,by decide⟩
theorem reservation (a b : Value) (same : Same a b) : a.reservation=b.reservation := by
 simpa [field] using same ⟨13,by decide⟩ ⟨0,by decide⟩ ⟨0,by decide⟩
theorem transcript_next (a b : Value) (same : Same a b) : a.transcript.next_row=b.transcript.next_row := by
 apply UScalar.eq_of_val_eq
 simpa [field] using same ⟨16,by decide⟩ ⟨0,by decide⟩ ⟨0,by decide⟩
#print axioms running
#print axioms terminal
#print axioms mask
#print axioms z0_x
#print axioms z0_y
#print axioms z1_x
#print axioms z1_y
#print axioms challenges_lambda
#print axioms challenges_chi
#print axioms challenges_theta
#print axioms challenges_mu
#print axioms challenges_eta
#print axioms alpha
#print axioms extra
#print axioms before
#print axioms challenges_zc
#print axioms state
#print axioms rest
#print axioms transcript_state
#print axioms claims_value
#print axioms claims_identity
#print axioms reservation
#print axioms transcript_next
end AspisR1.NMC_Frame
end
