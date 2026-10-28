import PV_L2C_HashRange
import PV_L2C_GeneratedRange
import PV_L2C_DigestRange
set_option autoImplicit false
namespace PV_L2C_DigestOrigin
open Aeneas Aeneas.Std Result R1Z R0Z.WriterRefine BuilderForestAdmissionPort
local instance : ExternalLinear := PV_Src_ExternalReference.dictionary

/-- Sources of raw digest words on the reviewed routes. This carrier stores
decoder/generator/hash executions, rather than the N3 guard's conclusion. -/
inductive Origin (d : Array U32 8#usize) : Prop where
  | decoded (bytes : Array U8 32#usize)
      (returned : AspisR1TerminalDecoder.atomic_statement.decode_digest_canonical bytes = ok (.Ok d))
  | generated (prior : Fin 8 → U32)
      (returned : ∀ j : Fin 8, d.val[j.val]! = PV_L2C_GeneratedRange.remainder (prior j))
  | hashed (domain : U32) (input : Slice U32)
      (domainBound : domain.val < 2147483647)
      (lengthBound : input.val.length < 2147483647) (nonempty : input.val ≠ [])
      (returned : poseidon2.hash_fields domain input = ok d)

theorem canonical (d : Array U32 8#usize) (h : Origin d) : Canon8 d := by
  cases h with
  | decoded bytes returned =>
    intro j hj
    apply PV_L2C_DigestRange.digest_success bytes d returned
    have hb : j < d.val.length := by simpa only [d.property,UScalar.ofNatCore_val_eq] using hj
    rw [getElem!_pos d.val j hb]
    exact List.getElem_mem hb
  | generated prior returned =>
    intro j hj
    rw [returned ⟨j,hj⟩]
    exact PV_L2C_GeneratedRange.remainder_range _
  | hashed domain input hd hl hn hr =>
    exact PV_L2C_HashRange.success domain input d hd hl hn hr
#print axioms canonical

theorem excludes_P (d : Array U32 8#usize) (h : Origin d) :
    ∀ j : Fin 8, d.val[j.val]! ≠ 2147483647#u32 := by
  intro j he
  have hb := canonical d h j.val j.isLt
  rw [he] at hb
  exact Nat.lt_irrefl 2147483647 hb
#print axioms excludes_P
end PV_L2C_DigestOrigin
