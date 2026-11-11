import R1PublicByteCodec

set_option autoImplicit false
namespace AspisR1.PublicByteCodec
open R0P AspisV8R15.ExactTowerBase

namespace PrefixCodec
variable {A B : Type}

theorem fixed_lawful (n : Nat) (emit : A → Bytes) (dec : Bytes → Option A)
    (hlen : ∀ a, (emit a).length = n)
    (hround : ∀ a, dec (emit a) = some a)
    (hback : ∀ bytes a, dec bytes = some a → emit a = bytes) :
    Lawful (fixed n emit dec) := by
  constructor
  · intro a rest
    have ht : (emit a ++ rest).take n = emit a := by
      rw [List.take_append_of_le_length (by rw [hlen a]),
        List.take_of_length_le (by rw [hlen a])]
    have hd : (emit a ++ rest).drop n = rest := by
      rw [List.drop_append_of_le_length (by rw [hlen a]),
        List.drop_of_length_le (by rw [hlen a]), List.nil_append]
    simp only [fixed, ht, hd, hround, Option.map_some]
  · intro bytes a rest h
    change (dec (bytes.take n)).map (fun x => (x, bytes.drop n)) = some (a, rest) at h
    cases hd : dec (bytes.take n) with
    | none => simp [hd] at h
    | some x =>
        have hp : (x, bytes.drop n) = (a, rest) := by simpa [hd] using h
        have hx : x = a := congrArg Prod.fst hp
        have hr : bytes.drop n = rest := congrArg Prod.snd hp
        calc
          emit a ++ rest = bytes.take n ++ bytes.drop n := by
            rw [← hx, ← hr, hback (bytes.take n) x hd]
          _ = bytes := List.take_append_drop n bytes

theorem pair_lawful (c : PrefixCodec A) (d : PrefixCodec B)
    (hc : Lawful c) (hd : Lawful d) : Lawful (pair c d) := by
  constructor
  · rintro ⟨a, b⟩ rest
    simp [pair, List.append_assoc, hc.round, hd.round]
  · rintro bytes ⟨a, b⟩ rest h
    cases hc0 : c.parse bytes with
    | none => simp [pair, hc0] at h
    | some ar =>
        rcases ar with ⟨a', mid⟩
        cases hd0 : d.parse mid with
        | none => simp [pair, hc0, hd0] at h
        | some br =>
            rcases br with ⟨b', last⟩
            have heq : ((a', b'), last) = ((a, b), rest) := by
              simpa [pair, hc0, hd0] using h
            have ha : a' = a := congrArg (fun z : (A × B) × Bytes => z.1.1) heq
            have hb : b' = b := congrArg (fun z : (A × B) × Bytes => z.1.2) heq
            have hr : last = rest := congrArg (fun z : (A × B) × Bytes => z.2) heq
            change (c.emit a ++ d.emit b) ++ rest = bytes
            rw [← ha, ← hb, ← hr, List.append_assoc, hd.back mid b' last hd0]
            exact hc.back bytes a' mid hc0

theorem transport_lawful (e : A ≃ B) (c : PrefixCodec A)
    (hc : Lawful c) : Lawful (transport e c) := by
  constructor
  · intro b rest
    simp [transport, hc.round]
  · intro bytes b rest h
    cases hp : c.parse bytes with
    | none => simp [transport, hp] at h
    | some ar =>
        rcases ar with ⟨a, tail⟩
        have heq : (e a, tail) = (b, rest) := by simpa [transport, hp] using h
        have hb : e a = b := congrArg Prod.fst heq
        have hr := congrArg Prod.snd heq
        dsimp only at hr
        change c.emit (e.symm b) ++ rest = bytes
        rw [← hb, e.symm_apply_apply, ← hr]
        exact hc.back bytes a tail hp

theorem option_lawful (c : PrefixCodec A) (hc : Lawful c) :
    Lawful (option c) := by
  constructor
  · intro oa rest
    cases oa <;> simp [option, hc.round]
  · intro bytes oa rest h
    cases bytes with
    | nil => simp [option] at h
    | cons tag tail =>
        by_cases h0 : tag = 0
        · have heq : (none, tail) = (oa, rest) := by
            simpa [option, h0] using h
          have ho := congrArg Prod.fst heq
          dsimp only at ho
          have hr := congrArg Prod.snd heq
          dsimp only at hr
          rw [← ho, ← hr]
          simp [option, h0]
        · by_cases h1 : tag = 1
          · cases hp : c.parse tail with
            | none => simp [option, h0, h1, hp] at h
            | some ar =>
                rcases ar with ⟨a, last⟩
                have heq : (some a, last) = (oa, rest) := by
                  simpa [option, h0, h1, hp] using h
                have ho := congrArg Prod.fst heq
                dsimp only at ho
                have hr := congrArg Prod.snd heq
                dsimp only at hr
                rw [← ho, ← hr]
                change (1 :: c.emit a) ++ last = tag :: tail
                simpa only [List.cons_append, h1] using
                  congrArg (List.cons (1 : Byte)) (hc.back tail a last hp)
          · simp [option, h0, h1] at h

theorem fixed_short (n : Nat) (emit : A → Bytes) (dec : Bytes → Option A)
    (hlen : ∀ a, (emit a).length = n)
    (hback : ∀ bytes a, dec bytes = some a → emit a = bytes)
    (bytes : Bytes) (hshort : bytes.length < n) :
    (fixed n emit dec).parse bytes = none := by
  cases hd : dec (bytes.take n) with
  | none => simp [fixed, hd]
  | some a =>
      have hb := hback (bytes.take n) a hd
      have heq : n = min n bytes.length := by
        simpa [hlen, List.length_take] using congrArg List.length hb
      omega

theorem option_invalid_tag (c : PrefixCodec A) (tag : Byte) (tail : Bytes)
    (h0 : tag ≠ 0) (h1 : tag ≠ 1) :
    (option c).parse (tag :: tail) = none := by
  simp [option, h0, h1]

theorem pair_left_failure (c : PrefixCodec A) (d : PrefixCodec B)
    (bytes : Bytes) (h : c.parse bytes = none) :
    (pair c d).parse bytes = none := by simp [pair, h]

theorem pair_right_failure (c : PrefixCodec A) (d : PrefixCodec B)
    (bytes mid : Bytes) (a : A) (hc : c.parse bytes = some (a, mid))
    (hd : d.parse mid = none) :
    (pair c d).parse bytes = none := by simp [pair, hc, hd]

end PrefixCodec

theorem variant_lawful : PrefixCodec.Lawful variantCodec := by
  constructor
  · intro v rest
    cases v <;> simp [variantCodec]
  · intro bytes v rest h
    cases bytes with
    | nil => simp [variantCodec] at h
    | cons tag tail =>
        by_cases h0 : tag = 0
        · have heq : (Variant.privateTransfer, tail) = (v, rest) := by
            simpa [variantCodec, h0] using h
          have hv := congrArg Prod.fst heq
          dsimp only at hv
          have hr := congrArg Prod.snd heq
          dsimp only at hr
          rw [← hv, ← hr]
          simp [variantCodec, h0]
        · by_cases h1 : tag = 1
          · have heq : (Variant.withdrawal, tail) = (v, rest) := by
              simpa [variantCodec, h0, h1] using h
            have hv := congrArg Prod.fst heq
            dsimp only at hv
            have hr := congrArg Prod.snd heq
            dsimp only at hr
            rw [← hv, ← hr]
            simp [variantCodec, h1]
          · simp [variantCodec, h0, h1] at h

theorem variant_invalid_tag (tag : Byte) (tail : Bytes)
    (h0 : tag ≠ 0) (h1 : tag ≠ 1) : variantCodec.parse (tag :: tail) = none := by
  simp [variantCodec, h0, h1]

theorem encodeU32_length (x : RetainedFieldByteCodec.RawWord) :
    (encodeU32 x).length = 4 := by simp [encodeU32]

theorem decodeU32_encode (x : RetainedFieldByteCodec.RawWord) :
    decodeU32 (encodeU32 x) = some x := by
  change (RetainedFieldByteCodec.fixedBytes? 4 (List.ofFn (RetainedFieldByteCodec.encodeWordLE x))).map RetainedFieldByteCodec.decodeWordLE = some x
  rw [ListFieldCodec.fixedBytes?_ofFn, Option.map_some, RetainedFieldByteCodec.decodeWordLE_encodeWordLE]

theorem encodeU32_of_decode (bytes : Bytes) (x : RetainedFieldByteCodec.RawWord)
    (h : decodeU32 bytes = some x) : encodeU32 x = bytes := by
  cases hf : RetainedFieldByteCodec.fixedBytes? 4 bytes with
  | none => simp [decodeU32, hf] at h
  | some word =>
      have hw : RetainedFieldByteCodec.decodeWordLE word = x := by
        simpa [decodeU32, hf] using h
      calc
        encodeU32 x = List.ofFn word := by
          rw [← hw, encodeU32, RetainedFieldByteCodec.encodeWordLE_decodeWordLE]
        _ = bytes := ListFieldCodec.fixedBytes?_sound 4 bytes word hf

theorem u32_lawful : PrefixCodec.Lawful u32Codec :=
  PrefixCodec.fixed_lawful 4 encodeU32 decodeU32
    encodeU32_length decodeU32_encode encodeU32_of_decode

theorem u64_lawful : PrefixCodec.Lawful u64Codec :=
  PrefixCodec.transport_lawful u64Equiv (PrefixCodec.pair u32Codec u32Codec)
    (PrefixCodec.pair_lawful u32Codec u32Codec u32_lawful u32_lawful)

theorem u64_emit_length (x : U64) : (u64Codec.emit x).length = 8 := by
  change (encodeU32 (u64Equiv.symm x).1 ++ encodeU32 (u64Equiv.symm x).2).length = 8
  simp [encodeU32_length]

theorem m31_lawful : PrefixCodec.Lawful m31Codec :=
  PrefixCodec.fixed_lawful 4 ExactLeafFieldCodec.encodeM31 ExactLeafFieldCodec.decodeM31
    ExactLeafFieldCodec.encodeM31_length ExactLeafFieldCodec.decodeM31_encodeM31
    ExactLeafFieldCodec.encodeM31_of_decodeM31

theorem encodeDigest_length (d : Digest M31Exact) : (encodeDigest d).length = 32 := by
  unfold encodeDigest FixedWidthDecoder.encode
  simp [List.length_flatMap, List.length_ofFn, ExactLeafFieldCodec.encodeM31_length]

theorem decodeDigest_encode (d : Digest M31Exact) : decodeDigest (encodeDigest d) = some d :=
  FixedWidthDecoder.decode_encode ExactLeafFieldCodec.decodeM31 ExactLeafFieldCodec.encodeM31
    4 8 d ExactLeafFieldCodec.encodeM31_length ExactLeafFieldCodec.decodeM31_encodeM31

theorem encodeDigest_of_decode (bytes : Bytes) (d : Digest M31Exact)
    (h : decodeDigest bytes = some d) : encodeDigest d = bytes :=
  FixedWidthDecoder.encode_of_decode ExactLeafFieldCodec.decodeM31 ExactLeafFieldCodec.encodeM31
    4 8 bytes d h ExactLeafFieldCodec.encodeM31_of_decodeM31

theorem digest_lawful : PrefixCodec.Lawful digestCodec :=
  PrefixCodec.fixed_lawful 32 encodeDigest decodeDigest
    encodeDigest_length decodeDigest_encode encodeDigest_of_decode

theorem encodeFrontier_length (f : Frontier) : (encodeFrontier f).length = 640 := by
  unfold encodeFrontier FixedWidthDecoder.encode
  simp [List.length_flatMap, List.length_ofFn, encodeDigest_length]

theorem decodeFrontier_encode (f : Frontier) : decodeFrontier (encodeFrontier f) = some f :=
  FixedWidthDecoder.decode_encode decodeDigest encodeDigest 32 20 f
    encodeDigest_length decodeDigest_encode

theorem encodeFrontier_of_decode (bytes : Bytes) (f : Frontier)
    (h : decodeFrontier bytes = some f) : encodeFrontier f = bytes :=
  FixedWidthDecoder.encode_of_decode decodeDigest encodeDigest 32 20 bytes f h
    encodeDigest_of_decode

theorem frontier_lawful : PrefixCodec.Lawful frontierCodec :=
  PrefixCodec.fixed_lawful 640 encodeFrontier decodeFrontier
    encodeFrontier_length decodeFrontier_encode encodeFrontier_of_decode

theorem fields_lawful : PrefixCodec.Lawful fieldsCodec := by
  unfold fieldsCodec
  apply PrefixCodec.pair_lawful _ _ variant_lawful
  apply PrefixCodec.pair_lawful _ _ digest_lawful
  apply PrefixCodec.pair_lawful _ _ digest_lawful
  apply PrefixCodec.pair_lawful _ _ m31_lawful
  apply PrefixCodec.pair_lawful _ _ (PrefixCodec.option_lawful _ digest_lawful)
  apply PrefixCodec.pair_lawful _ _ digest_lawful
  apply PrefixCodec.pair_lawful _ _ (PrefixCodec.option_lawful _ m31_lawful)
  apply PrefixCodec.pair_lawful _ _ u64_lawful
  apply PrefixCodec.pair_lawful _ _ frontier_lawful
  exact PrefixCodec.pair_lawful _ _ digest_lawful frontier_lawful

theorem public_lawful : PrefixCodec.Lawful publicCodec :=
  PrefixCodec.transport_lawful publicFieldsEquiv.symm fieldsCodec fields_lawful

theorem parseRaw_emit_suffix (pub : WirePublic) (rest : Bytes) :
    parseRaw (publicCodec.emit pub ++ rest) =
      if rest = [] then some pub.val else none := by
  simp [parseRaw, public_lawful.round]

theorem parseRaw_emit (pub : WirePublic) : parseRaw (publicCodec.emit pub) = some pub.val := by
  simpa using parseRaw_emit_suffix pub []

theorem encode_success_bound (pub : BasePublic) (bytes : Bytes)
    (h : encode pub = some bytes) : pub.nextPairIndex < 2^64 := by
  unfold encode at h
  split at h
  · assumption
  · simp at h

theorem parseRaw_eq_some_iff (bytes : Bytes) (pub : BasePublic) :
    parseRaw bytes = some pub ↔ encode pub = some bytes := by
  constructor
  · intro h
    unfold parseRaw at h
    cases hp : publicCodec.parse bytes with
    | none => simp [hp] at h
    | some qr =>
        rcases qr with ⟨q, rest⟩
        by_cases hr : rest = []
        · have hv : q.val = pub := by simpa [hp, hr] using h
          have hb : publicCodec.emit q = bytes := by
            simpa [hr] using public_lawful.back bytes q rest hp
          have hi : pub.nextPairIndex < 2^64 := by rw [← hv]; exact q.property
          have hq : (⟨pub, hi⟩ : WirePublic) = q := Subtype.ext hv.symm
          simp only [encode, dif_pos hi, hq, hb]
        · simp [hp, hr] at h
  · intro h
    unfold encode at h
    split at h
    next hi =>
      have hb : publicCodec.emit (⟨pub, hi⟩ : WirePublic) = bytes := Option.some.inj h
      rw [← hb]
      exact parseRaw_emit ⟨pub, hi⟩
    next hi => simp at h

theorem decode_eq_some_iff (bytes : Bytes) (pub : BasePublic) :
    decode bytes = some pub ↔
      encode pub = some bytes ∧ PublicOptionShape.check pub = true := by
  constructor
  · intro h
    cases hp : parseRaw bytes with
    | none => simp [decode, hp] at h
    | some q =>
        by_cases hc : PublicOptionShape.check q = true
        · have hq : q = pub := by simpa [decode, hp, hc] using h
          subst q
          exact ⟨(parseRaw_eq_some_iff bytes pub).mp hp, hc⟩
        · simp [decode, hp, hc] at h
  · rintro ⟨he, hc⟩
    have hp := (parseRaw_eq_some_iff bytes pub).mpr he
    simp [decode, hp, hc]

theorem decode_of_encode (pub : BasePublic) (bytes : Bytes)
    (he : encode pub = some bytes) (hc : PublicOptionShape.canonical pub) :
    decode bytes = some pub :=
  (decode_eq_some_iff bytes pub).mpr
    ⟨he, (PublicOptionShape.check_eq_true_iff pub).mpr hc⟩

theorem encode_of_decode (bytes : Bytes) (pub : BasePublic)
    (h : decode bytes = some pub) : encode pub = some bytes :=
  ((decode_eq_some_iff bytes pub).mp h).1

theorem decode_canonical (bytes : Bytes) (pub : BasePublic)
    (h : decode bytes = some pub) : PublicOptionShape.canonical pub :=
  (PublicOptionShape.check_eq_true_iff pub).mp ((decode_eq_some_iff bytes pub).mp h).2

theorem decode_index_lt (bytes : Bytes) (pub : BasePublic)
    (h : decode bytes = some pub) : pub.nextPairIndex < 2^64 :=
  encode_success_bound pub bytes (encode_of_decode bytes pub h)

theorem roundtrip (pub : BasePublic) (hi : pub.nextPairIndex < 2^64)
    (hc : PublicOptionShape.canonical pub) :
    ∃ bytes, encode pub = some bytes ∧ decode bytes = some pub := by
  have he : encode pub = some (publicCodec.emit (⟨pub, hi⟩ : WirePublic)) := by
    simp only [encode, dif_pos hi]
  exact ⟨_, he, decode_of_encode pub _ he hc⟩

theorem parseRaw_trailing (pub : WirePublic) (rest : Bytes) (hne : rest ≠ []) :
    parseRaw (publicCodec.emit pub ++ rest) = none := by
  rw [parseRaw_emit_suffix, if_neg hne]

theorem decode_trailing (pub : WirePublic) (rest : Bytes) (hne : rest ≠ []) :
    decode (publicCodec.emit pub ++ rest) = none := by
  simp [decode, parseRaw_trailing pub rest hne]

theorem parseRaw_strict_prefix (pub : WirePublic) (preBytes suffix : Bytes)
    (he : publicCodec.emit pub = preBytes ++ suffix) (hne : suffix ≠ []) :
    parseRaw preBytes = none := by
  cases hr : parseRaw preBytes with
  | none => rfl
  | some q =>
      have hq := (parseRaw_eq_some_iff preBytes q).mp hr
      have hi := encode_success_bound q preBytes hq
      let wq : WirePublic := ⟨q, hi⟩
      have heq : publicCodec.emit wq = preBytes := by
        simpa only [encode, dif_pos hi, Option.some.injEq] using hq
      have hp : publicCodec.parse (publicCodec.emit pub) = some (pub, []) := by
        simpa using public_lawful.round pub []
      have hqp : publicCodec.parse (publicCodec.emit pub) = some (wq, suffix) := by
        rw [he, ← heq]
        exact public_lawful.round wq suffix
      have hs : (pub, []) = (wq, suffix) := Option.some.inj (hp.symm.trans hqp)
      exact False.elim (hne (congrArg Prod.snd hs).symm)

theorem parseRaw_truncated (pub : WirePublic) (n : Nat)
    (hn : n < (publicCodec.emit pub).length) :
    parseRaw ((publicCodec.emit pub).take n) = none := by
  apply parseRaw_strict_prefix pub _ ((publicCodec.emit pub).drop n)
    (List.take_append_drop n (publicCodec.emit pub)).symm
  intro hz
  have hl := congrArg List.length hz
  simp only [List.length_drop, List.length_nil] at hl
  omega

theorem decode_truncated (pub : WirePublic) (n : Nat)
    (hn : n < (publicCodec.emit pub).length) :
    decode ((publicCodec.emit pub).take n) = none := by
  simp [decode, parseRaw_truncated pub n hn]

theorem parseRaw_bad_variant (tag : Byte) (tail : Bytes)
    (h0 : tag ≠ 0) (h1 : tag ≠ 1) : parseRaw (tag :: tail) = none := by
  have hb := variant_invalid_tag tag tail h0 h1
  simp [parseRaw, publicCodec, PrefixCodec.transport, fieldsCodec, PrefixCodec.pair, hb]

theorem parseRaw_bad_recipient_tag
    (v : Variant) (anchor nullifier : Digest M31Exact) (asset : M31Exact)
    (tag : Byte) (tail : Bytes) (h0 : tag ≠ 0) (h1 : tag ≠ 1) :
    parseRaw (variantCodec.emit v ++ digestCodec.emit anchor ++
      digestCodec.emit nullifier ++ m31Codec.emit asset ++ (tag :: tail)) = none := by
  have hb := PrefixCodec.option_invalid_tag digestCodec tag tail h0 h1
  simp [parseRaw, publicCodec, PrefixCodec.transport, fieldsCodec, PrefixCodec.pair,
    List.append_assoc, variant_lawful.round, digest_lawful.round, m31_lawful.round, hb]

theorem parseRaw_bad_amount_tag
    (v : Variant) (anchor nullifier : Digest M31Exact) (asset : M31Exact)
    (recipient : Option (Digest M31Exact)) (change : Digest M31Exact)
    (tag : Byte) (tail : Bytes) (h0 : tag ≠ 0) (h1 : tag ≠ 1) :
    parseRaw (variantCodec.emit v ++ digestCodec.emit anchor ++
      digestCodec.emit nullifier ++ m31Codec.emit asset ++
      (PrefixCodec.option digestCodec).emit recipient ++ digestCodec.emit change ++
      (tag :: tail)) = none := by
  have ho := PrefixCodec.option_lawful digestCodec digest_lawful
  have hb := PrefixCodec.option_invalid_tag m31Codec tag tail h0 h1
  simp [parseRaw, publicCodec, PrefixCodec.transport, fieldsCodec, PrefixCodec.pair,
    List.append_assoc, variant_lawful.round, digest_lawful.round, m31_lawful.round,
    ho.round, hb]

theorem decode_zero_withdrawal (bytes : Bytes) (pub : BasePublic)
    (hp : parseRaw bytes = some pub) (hv : pub.variant = .withdrawal)
    (ha : pub.withdrawalAmount = some 0) : decode bytes = none := by
  have hc : PublicOptionShape.check pub = false := by
    simp [PublicOptionShape.check, hv, ha]
  simp [decode, hp, hc]

theorem encode_unique (bytes : Bytes) (p q : BasePublic)
    (hp : encode p = some bytes) (hq : encode q = some bytes) : p = q := by
  have h1 := (parseRaw_eq_some_iff bytes p).mpr hp
  have h2 := (parseRaw_eq_some_iff bytes q).mpr hq
  exact Option.some.inj (h1.symm.trans h2)

#print axioms PrefixCodec.fixed_lawful
#print axioms PrefixCodec.pair_lawful
#print axioms PrefixCodec.transport_lawful
#print axioms PrefixCodec.option_lawful
#print axioms u32_lawful
#print axioms u64_lawful
#print axioms digest_lawful
#print axioms frontier_lawful
#print axioms public_lawful
#print axioms parseRaw_eq_some_iff
#print axioms decode_eq_some_iff
#print axioms roundtrip
#print axioms parseRaw_trailing
#print axioms parseRaw_truncated
#print axioms parseRaw_bad_variant
#print axioms parseRaw_bad_recipient_tag
#print axioms parseRaw_bad_amount_tag
#print axioms decode_zero_withdrawal
#print axioms encode_unique
end AspisR1.PublicByteCodec
