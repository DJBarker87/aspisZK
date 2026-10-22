import R1Z.ProverCommitPublicPrefix41

/-! Explicit separation of the two raw private seed families from both
public bindings. The statement digest address remains in the existing
protocol frozen-address obligation; it is not declared disjoint. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverCommitRawFresh42
open R0Z.FsStatement R1Z.LensR1 R1Z.LayoutR1PBin
attribute [local instance] Classical.propDecidable

def domain (i : Fin 3) : List UInt8 :=
  if i.val = 0 then dMaskSeed else if i.val = 1 then dSourceSeed else dLeafSalt

/-- Tiny fixed-domain comparison only; arbitrary trailing inputs are never
normalised. The two field domains share a private seed. -/
theorem ne_binding (i : Fin 3) (tail more : List UInt8) (b : Fin 2) :
    domain i ++ tail ≠ (if b.val = 0 then dBind0 else dBind1) ++ more := by
  intro eq
  by_cases hb : b.val = 0
  · have head := congrArg (fun bs : List UInt8 => bs.head?) eq
    fin_cases i <;> simp [domain,hb,dMaskSeed,dSourceSeed,dLeafSalt,dBind0] at head
  · by_cases hi : i.val = 1
    · have byte := congrArg (fun bs : List UInt8 => bs[25]?) eq
      simp [domain,hi,hb,dSourceSeed,dBind1] at byte
    · have byte := congrArg (fun bs : List UInt8 => bs[18]?) eq
      fin_cases i <;> simp_all [domain,dMaskSeed,dSourceSeed,dLeafSalt,dBind1]

/-- Extending the earlier public query ledger with the two binding reads
does not introduce a private raw derivation hit. -/
theorem raw_off_bindings (i : Fin 3) (frame : List UInt8) (seed : OracleAnswer)
    (pub : List UInt8) (tag : UInt8) (digest nonce first : OracleAnswer) :
    domain i ++ frame ++ List.ofFn seed ≠ ProverCommitPublicBinding40.binding pub tag digest nonce ∧
    domain i ++ frame ++ List.ofFn seed ≠ ProverCommitPublicPrefix41.binding1 digest nonce first := by
  constructor
  · simpa only [ProverCommitPublicBinding40.binding,List.append_assoc,Fin.val_zero,if_true] using
      ne_binding i (frame ++ List.ofFn seed) (pub ++ [tag] ++ ctxEnc digest nonce) 0
  · simpa only [ProverCommitPublicPrefix41.binding1,List.append_assoc,Fin.val_one,if_false,show ¬(1 : Nat) = 0 from by decide] using
      ne_binding i (frame ++ List.ofFn seed) (ans first ++ ctxEnc digest nonce ++ descr) 1

/-- No new event is charged for the binding reads. The statement-address
case is deliberately left separate, as in the previous protocol-ROM proof. -/
theorem raw_off_prefix (history : List ProverCommitSeedEvent19.Entry)
    (seed : OracleAnswer) (off : ¬ ProverCommitPrivateMemo40.guessed history seed)
    (i : Fin 3) (frame pub : List UInt8) (tag : UInt8)
    (digest nonce first : OracleAnswer) (statement : domain i ++ frame ++ List.ofFn seed ≠ pub) :
    domain i ++ frame ++ List.ofFn seed ∉
      history.map Prod.fst ++ ProverCommitPublicPrefix41.inputs pub tag nonce digest first := by
  intro member
  rcases List.mem_append.mp member with old | added
  · obtain ⟨e,he,same⟩ := List.mem_map.mp old
    exact ProverCommitPublicPrefix41.raw_off_history history seed off
      (domain i ++ frame) e he same.symm
  · have separated := raw_off_bindings i frame seed pub tag digest nonce first
    have excluded := (show ¬ (domain i ++ frame ++ List.ofFn seed = pub ∨
        domain i ++ frame ++ List.ofFn seed = ProverCommitPublicBinding40.binding pub tag digest nonce ∨
        domain i ++ frame ++ List.ofFn seed = ProverCommitPublicPrefix41.binding1 digest nonce first) from
        fun h => h.elim statement (fun h => h.elim separated.1 separated.2))
    apply excluded
    simpa only [ProverCommitPublicPrefix41.inputs,List.mem_cons,List.not_mem_nil,or_false] using added

#print axioms ne_binding
#print axioms raw_off_bindings
#print axioms raw_off_prefix
end R1Z.ProverCommitRawFresh42
