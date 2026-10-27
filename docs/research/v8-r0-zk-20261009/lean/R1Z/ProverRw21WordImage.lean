import R1Z.ProverRw21ByteCarrier
set_option autoImplicit false
namespace R1Z.ProverRw21WordImage
open Aeneas Aeneas.Std ProverRw21ByteCarrier
open AspisR1.RetainedFieldByteCodec

theorem ofFin_toFin (b : UInt8) : UInt8.ofFin b.toFin=b := by cases b; rfl

theorem decoded (x : U32) :
    (core.num.U32.to_le_bytes x).val.map decode =
      (List.ofFn (encodeWordLE (ProverCommitWordBytes47.rawWord x))).map UInt8.ofFin := by
  have h := congrArg (List.map UInt8.ofFin) (word_bytes x)
  simpa only [List.map_map,Function.comp_def,ofFin_toFin,List.map_id_fun] using h

theorem byte_mod (n : Nat) : UInt8.ofFin ⟨n%256,Nat.mod_lt _ (by decide)⟩=UInt8.ofNat (n%256) := by
  apply UInt8.toNat_inj.mp
  change n%256=(n%256)%256
  rw [Nat.mod_mod]

theorem model_word (x : U32) :
    (List.ofFn (encodeWordLE (ProverCommitWordBytes47.rawWord x))).map UInt8.ofFin =
      ProverRw21ProtocolOutput.word x.val := by
  change [UInt8.ofFin ⟨x.val%256,_⟩,
    UInt8.ofFin ⟨(x.val/256)%256,_⟩,
    UInt8.ofFin ⟨(x.val/65536)%256,_⟩,
    UInt8.ofFin ⟨(x.val/16777216)%256,_⟩]=_
  rw [byte_mod,byte_mod,byte_mod,byte_mod]
  unfold ProverRw21ProtocolOutput.word
  simp only [List.range_succ,List.range_zero,List.map_append,List.map_cons,List.map_nil,
    List.nil_append,List.cons_append,List.append_nil,pow_zero,pow_one,Nat.div_one]
  rfl

theorem source_word (x : U32) :
    (core.num.U32.to_le_bytes x).val.map decode=ProverRw21ProtocolOutput.word x.val := by
  rw [decoded,model_word]

#print axioms ofFin_toFin
#print axioms decoded
#print axioms byte_mod
#print axioms model_word
#print axioms source_word
end R1Z.ProverRw21WordImage
