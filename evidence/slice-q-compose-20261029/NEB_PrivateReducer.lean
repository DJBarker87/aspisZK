import LPf_ReductionWord
import NEB_ReducerCall
import NEB_CMCarrier
import NEB_PureFrame
set_option autoImplicit false
namespace NEB_PrivateReducer
open Aeneas Aeneas.Std Result AspisR1

/-- No fixture or private-Q canonicality hypothesis is needed: this scalar
helper consumes every U64 independently of the enclosing dot history. -/
theorem reference (x : U64) :
    FIo_Native.fast_pairing.canonical.reduce x=NEB_Reference.reference x := by
  obtain ⟨a,ha,va,ca⟩ := LPf_ReductionWord.native_reduce x
  obtain ⟨b,hb,_,vb,cb⟩ := NEB_ReducerCall.value x
  have same : a=b := UScalar.eq_of_val_eq (va.trans vb.symm)
  rw [ha,hb,same]

theorem frame {S Event : Type} (state : S) (x : U64) : ∃ z : U32,
    FIo_Native.fast_pairing.canonical.reduce x=ok z ∧
    NEB_Reference.reference x=ok z ∧
    z.val=x.val%2147483647 ∧ z.val<2147483647 ∧
    NEB_PureFrame.run (Event:=Event) state
      (FIo_Native.fast_pairing.canonical.reduce x)=ok (z,state,[]) := by
  obtain ⟨z,hz,vz,cz⟩ := LPf_ReductionWord.native_reduce x
  exact ⟨z,hz,by rw [← reference];exact hz,vz,cz,by rw [hz];rfl⟩

/-- Each of the four frozen source u64::from(P) occurrences is this same
lossless scalar conversion; the source carries no private-Q input. -/
theorem constant_cast :
    (UScalar.cast .U64 (2147483647#u32)).val=2147483647 := by
  simpa using NEB_CMCarrier.lossless (2147483647#u32)

#print axioms reference
#print axioms frame
#print axioms constant_cast
end NEB_PrivateReducer
