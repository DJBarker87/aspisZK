import NKU_Chronology
import NKK_FieldStages
set_option autoImplicit false
noncomputable section
namespace NKU_FineRead
open Aeneas Aeneas.Std Result AspisR1 NID_ResumeEmission NJU_ResumeObserved
open NKU_Chronology
/-- Atomic parent-state writes for one native E/K/raw occurrence. The update
is a pure local-field assignment; roots instantiate it with fixed functions. -/
def e (write : NKU.E → NKU.Decoded → NKU.Decoded) : Stage Unit := fun s=>do
 let (reply,r) ← recordE s.reader
 NKK_Try.emitted reply (fun value=>pure (.Ok ((),{s with reader := r,decoded := write value s.decoded})))
def k (write : NKU.K → NKU.Decoded → NKU.Decoded) : Stage Unit := fun s=>do
 let (reply,r) ← recordK s.reader
 NKK_Try.emitted reply (fun value=>pure (.Ok ((),{s with reader := r,decoded := write value s.decoded})))
def raw (n : Usize) (write : Array U8 n → NKU.Decoded → NKU.Decoded) : Stage Unit := fun s=>do
 let (value,r) ← recordRaw n s.reader
 pure (.Ok ((),{s with reader := r,decoded := write value s.decoded}))
theorem e_bind {T : Type} (s : NKU.State) (write : NKU.E → NKU.Decoded → NKU.Decoded)
 (next : NKU.State → Run (core.result.Result T verifier.Error)) :
 (e write s >>= fun reply=>NKK_Try.emitted reply (fun (_,post)=>next post))=
 NKK_FieldStages.withE s.reader (fun value r=>next {s with reader := r,decoded := write value s.decoded}) := by
 unfold e NKK_FieldStages.withE
 simp only [NKK_LogAlgebra.bind_assoc,NKK_Try.branch,NKK_LogReduce.pure_bind]
 apply NKK_LogAlgebra.bind_congr
 rintro ⟨reply,r⟩
 cases reply <;> rfl
theorem k_bind {T : Type} (s : NKU.State) (write : NKU.K → NKU.Decoded → NKU.Decoded)
 (next : NKU.State → Run (core.result.Result T verifier.Error)) :
 (k write s >>= fun reply=>NKK_Try.emitted reply (fun (_,post)=>next post))=
 NKK_FieldStages.withK s.reader (fun value r=>next {s with reader := r,decoded := write value s.decoded}) := by
 unfold k NKK_FieldStages.withK
 simp only [NKK_LogAlgebra.bind_assoc,NKK_Try.branch,NKK_LogReduce.pure_bind]
 apply NKK_LogAlgebra.bind_congr
 rintro ⟨reply,r⟩
 cases reply <;> rfl
theorem raw_bind {T : Type} (s : NKU.State) (n : Usize)
 (write : Array U8 n → NKU.Decoded → NKU.Decoded)
 (next : NKU.State → Run (core.result.Result T verifier.Error)) :
 (raw n write s >>= fun reply=>NKK_Try.emitted reply (fun (_,post)=>next post))=
 (do let (value,r) ← recordRaw n s.reader
     next {s with reader := r,decoded := write value s.decoded}) := by
 unfold raw
 simp only [NKK_LogAlgebra.bind_assoc,NKK_Try.branch,NKK_LogReduce.pure_bind]
 apply NKK_LogAlgebra.bind_congr
 rintro ⟨value,r⟩
 rfl
#print axioms e_bind
#print axioms k_bind
#print axioms raw_bind
end NKU_FineRead
