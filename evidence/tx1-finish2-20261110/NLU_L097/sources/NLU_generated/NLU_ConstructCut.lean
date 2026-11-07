import NLU_Words
import NLU_Cell
set_option autoImplicit false
namespace AspisR1.NLU_Construct
open Aeneas Aeneas.Std AspisR1PublicPreparation
open NLU (word cell)
abbrev Value := r1_semantic.Verified Unit
structure Frame where
 expected : Value
structure Observation where
 value : Value
abbrev Native := Frame → Observation
/-- Tagged scalar/byte projection of the constructor's miscellaneous fields.
Matches construct_window mode3, with tag<13 and bounded word/array indices. -/
def misc (v : Value) (tag : Fin 13) (col : Fin 29) (ai : Fin 10) (byte : Fin 32) (j : Fin 4) : Nat :=
 match tag.val with
 | 0=>(word (cell v.extra col.val col.isLt) j).val
 | 1=>(word (cell v.before_z1 col.val col.isLt) j).val
 | 2=>(word v.challenges.lambda j).val
 | 3=>(word v.challenges.chi j).val
 | 4=>(word v.challenges.theta j).val
 | 5=>(word v.challenges.mu j).val
 | 6=>(word v.challenges.eta j).val
 | 7=>(word (cell v.challenges.zc ai.val ai.isLt) j).val
 | 8=>(word (cell v.z 0 (by decide)).x j).val
 | 9=>(word (cell v.z 0 (by decide)).y j).val
 | 10=>(word (cell v.z 1 (by decide)).x j).val
 | 11=>(word (cell v.z 1 (by decide)).y j).val
 | _=>(cell v.state_before_z0 byte.val byte.isLt).val
/-- programs/r1-cost-probe/src/NLU_program.rs SHA256
081a7249e92a16f46461172a7cb5f84a8c36a092e218408cb3dfd018226aea8c. Literal mode assertions: owner equality,
"word(out.claims[row][col],j)==expected", "word(out.alpha[ai],j)==ea",
"actual==expected_misc", selected root-byte equality and
"after[byte]==tstate[byte] && after_next==next" (K007..K018).
Value portion of the reviewed per-word/byte constructor transcription.
Physical owner/allocator/lifecycle integration is OPEN and is NOT supplied
by this value packet; K007/K008 are separately retained native support.
Hash carrier is Unit,
the actual deployed SolanaDigest's zero-sized value. No arbitrary-H hash fact
is asserted by a snapshot which only tests state bytes and next-row. The
native/semantic hash-carrier transport remains a separate parent obligation.
All fields below correspond to the six paired constructor modes; source and
KMX hashes are recorded in the native receipt/source pins. -/
def Cut (native : Native) : Prop := ∀ f,
 (∀ row : Fin 3,∀ col : Fin 29,∀ j,
  word (cell (cell (native f).value.claims row.val row.isLt) col.val col.isLt) j=
  word (cell (cell f.expected.claims row.val row.isLt) col.val col.isLt) j) ∧
 (∀ ai : Fin 10,∀ j,word (cell (native f).value.alpha ai.val ai.isLt) j=
  word (cell f.expected.alpha ai.val ai.isLt) j) ∧
 (∀ tag col ai byte j,misc (native f).value tag col ai byte j=misc f.expected tag col ai byte j) ∧
 (∀ root : Fin 2,∀ byte : Fin 32,
  cell (cell (native f).value.roots root.val root.isLt) byte.val byte.isLt=
  cell (cell f.expected.roots root.val root.isLt) byte.val byte.isLt) ∧
 (∀ byte : Fin 32,cell (native f).value.transcript.state byte.val byte.isLt=
  cell f.expected.transcript.state byte.val byte.isLt) ∧
 (native f).value.transcript.next=f.expected.transcript.next
end AspisR1.NLU_Construct
