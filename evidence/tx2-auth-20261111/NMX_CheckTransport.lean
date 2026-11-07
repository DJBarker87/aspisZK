import NMX_CommandTransport
set_option autoImplicit false
namespace NMX_CheckTransport
/-- One conditional occurrence; only the unblocked continuation is required. -/
theorem step {A : Type} (b : Bool) (m n : RSL.RS A)
 (suffix : NMX_Heterogeneous.Refines id m n) :
 NMX_Heterogeneous.Refines id
  (if b then RSL.RS.throw .invalidAccountData else m)
  (RSL.RS.bind (RSL.RS.check b .invalidAccountData) (fun _ => n)) := by
 cases b with
 | false => simpa [RSL.RS.check,RSL.RS.bind_pure] using suffix
 | true => simpa [RSL.RS.check,RSL.RS.bind_throw] using
    (NMX_CommandTransport.thrown (A:=A) (B:=A) id RSL.ProgramError.invalidAccountData)

#print axioms step
end NMX_CheckTransport
