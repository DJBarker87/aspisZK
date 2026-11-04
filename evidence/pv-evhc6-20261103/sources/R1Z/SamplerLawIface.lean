import Mathlib.Logic.Equiv.Defs

/-! Statement-only interface for the D47.2 sampler premise (DESIGN-BUILD-INTEGRATION §4 (c)).

The four fields of `R1Z.Sem1UniformR1.QM31SamplerLaw`, over the same carrier
`Fin 32 → UInt8` (= `R0Z.FsStatement.OracleAnswer`), with no typeclass on `K`.  The import
closure is Mathlib's `Equiv` only, so this module's object is the same on the privacy base and
on the spend-path base; a joint module on either base can produce a value of it, and
`Sem1UniformR1.QM31SamplerLaw` is obtained from it field by field. -/

set_option autoImplicit false

namespace R1Z.SamplerLawIface

/-- Rank the 32 bytes bijectively into `Fin 2^256`, reduce mod `p⁴`, embed injectively. -/
structure QM31SamplerLaw {K : Type} (s1 : (Fin 32 → UInt8) → K) where
  rank : (Fin 32 → UInt8) ≃ Fin (2 ^ 256)
  emb : Nat → K
  emb_inj : ∀ x y : Nat, x < (2 ^ 31 - 1) ^ 4 → y < (2 ^ 31 - 1) ^ 4 → emb x = emb y → x = y
  sample : ∀ b, s1 b = emb ((rank b).val % (2 ^ 31 - 1) ^ 4)

end R1Z.SamplerLawIface

#print axioms R1Z.SamplerLawIface.QM31SamplerLaw
