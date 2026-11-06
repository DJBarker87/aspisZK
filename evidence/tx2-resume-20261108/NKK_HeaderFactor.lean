import NKK_HeaderSource
import NKK_LogReduce
set_option autoImplicit false
noncomputable section
namespace NKK_HeaderFactor
open Aeneas Aeneas.Std Result AspisR1 NID_ResumeEmission NJU_ResumeObserved

/-- The header result feeds this actual digest/Reader continuation at the
same bytes and Reservation. Every prior reject and abort stays in place. -/
theorem source (reservation : NP6_StdModel.Reservation) {H : Type}
 (d : AspisR1Stage2.aspis_core.digest.Digest32 H) (bytes proof pub : Slice U8)
 (hash : H) :
 NJU_ResumeObserved.run reservation d bytes proof pub .S2 hash=
 (do let reply ← NKK_HeaderSource.header d bytes .S2
     NKK_Try.emitted reply (fun pair=>
       NKK_HeaderSource.afterHeader reservation d bytes proof pub .S2 hash pair.1 pair.2)) := by
 unfold NJU_ResumeObserved.run NKK_HeaderSource.header NKK_HeaderSource.afterHeader
 simp only [NKK_LogAlgebra.bind_assoc,NKK_LogReduce.pure_bind,NKK_Try.branch]
 repeat' first
 | rfl
 | (apply NKK_LogAlgebra.bind_congr;intro value)
 | split
 | (fail_if_no_progress simp only [NKK_LogAlgebra.bind_assoc,NKK_LogReduce.pure_bind,NKK_Try.branch,NJU_Log.prod_cases])

#print source
#print axioms source
end NKK_HeaderFactor
