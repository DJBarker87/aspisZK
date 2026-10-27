# Exact retained theorem statements

Statements copied from the pinned source files; proofs are reused, not freshly replayed by this diagnostic.

## docs/research/v8-full-view-zk-20260912/lean/AspisV8R19/SamplerClosureCircleFieldExecution.lean

SHA256 `89a9b0954a008fc382f5296974dabfffc7e370db1d8f8a4a0deb1c0a95ccaefe`.

```lean
theorem cm_inv (x : CM31Exact) (hx : x ≠ 0) :
    field.CM31.inv (encodeCM x) = .ok (encodeCM x⁻¹)
```

```lean
theorem try_inverse_nonzero (x : QM31Exact) (hx : x ≠ 0) :
    field.QM31.try_inv (encode x) = .ok (some (encode x⁻¹))
```

```lean
theorem try_inverse_zero : field.QM31.try_inv (encode 0) = .ok none
```

```lean
theorem square (x : QM31Exact) : field.QM31.square (encode x) = .ok (encode (x*x))
```

## docs/research/v8-full-view-zk-20260912/lean/AspisV8R19/SamplerClosureCircleScalarTransport.lean

SHA256 `4c8d644cf69d225fb31905620f48b22eb174d649905833216733a7beb182bde8`.

```lean
theorem inv_encode (x : M31Exact) (hx : x ≠ 0) :
    field.M31.inv (encodeBase x) = .ok (encodeBase x⁻¹)
```

## docs/research/v8-full-view-zk-20260912/lean/AspisV8R19/GeneratedInverseLoop.lean

SHA256 `5fece3cd96f333dc760819886958fafcbc5b7f66c5c97ed84d36f325a6c4cc4e`.

```lean
theorem square_n_exec (x : Word) (count : Usize) :
    aspis_core.field.square_n (encode x) count =
      .ok (encode (squares wordMul count.val x))
```

```lean
theorem inv_correct (self : aspis_core.field.M31)
    (hc : self.val < AspisV8R15.ExactTowerBase.P) (hne : self.val ≠ 0) :
    ∃ out : aspis_core.field.M31,
      aspis_core.field.M31.inv self = .ok out ∧
      out.val < AspisV8R15.ExactTowerBase.P ∧
      (out.val : AspisV8R15.ExactTowerBase.M31Exact) =
        (self.val : AspisV8R15.ExactTowerBase.M31Exact)⁻¹
```

## docs/research/v8-full-view-zk-20260912/lean/AspisV8R19/GuardedInverseExecution.lean

SHA256 `2f78aaef9a717afe45752e7282595ba6571fd6eb991f8d5fbf94856cc1dc1235`.

```lean
theorem inverse_correct (x : U32) (hc : x.val < AspisV8R15.ExactTowerBase.P)
    (hne : x.val ≠ 0) :
    ∃ out : U32, field.M31.inv x = .ok out ∧ out.val < AspisV8R15.ExactTowerBase.P ∧
      (out.val : AspisV8R15.ExactTowerBase.M31Exact) =
        (x.val : AspisV8R15.ExactTowerBase.M31Exact)⁻¹
```

## lean/SAQ_InverseFieldModel.lean

SHA256 `098052ad7327892176a4f883293e761f718c9015a56078702cc2bfaddb60d6b6`.

```lean
theorem current_inv_total_inverse (x : U32) (hx : decode x ≠ 0) :
    ∃ z, field.M31.inv AspisR1Qm31ArithmeticProbe.field.M31.mul x = .ok z ∧
      decode z = (decode x)⁻¹
```

## evidence/replay-dry8-20261026/RPz7_AspisR1CircleSampleWrapper_RawCircleSampleActualFallbackResultV4.lean

SHA256 `b14cebff174ab48e69378de9233b8f6f5a88137260c75c7ded6d97b753fd8bdb`.

```lean
theorem firstFallbackActual
    (block : Array Std.U8 32#usize) (q : field.QM31)
    (err : circle.CirclePointError)
    (hsample : sampler.qm31_sample block = ok q)
    (hcircle : circle.secure_ood_circle_point_from_parameter q = ok (.Err err)) :
    sampler.circle_sample block .First =
      .ok (fromFallbackPoint (AspisR1CircleFallback.fromR72Point
        (encodePoint (point circleFallbackParameter0))))
```

```lean
theorem secondFallbackActual
    (block : Array Std.U8 32#usize) (q : field.QM31)
    (err : circle.CirclePointError)
    (hsample : sampler.qm31_sample block = ok q)
    (hcircle : circle.secure_ood_circle_point_from_parameter q = ok (.Err err)) :
    sampler.circle_sample block .Second =
      .ok (fromFallbackPoint (AspisR1CircleFallback.fromR72Point
        (encodePoint (point circleFallbackParameter1))))
```

## evidence/replay-dry8-20261026/RPz7_AspisR1CircleSampleWrapper_RawCircleSampleActualPolicyUnconditionalV1.lean

SHA256 `483aae0f2bfb5e7d807bab429c102311529c48eb7a6f814f21d18e022ab58e7e`.

```lean
theorem sampler_total_canonical (block : Array Std.U8 32#usize) :
    ∃ q : field.QM31, sampler.qm31_sample block = .ok q ∧ Canonical (toR72QM q)
```

```lean
theorem circle_sample_total_on_circle
    (block : Array Std.U8 32#usize) (row : r0_transcript.CircleRow) :
    ∃ p : circle.SecureCirclePoint,
      sampler.circle_sample block row = .ok p ∧
      RawCircleSampleActualPolicyV1.R0PCirclePoint p
```

## evidence/replay-dry8-20261026/RPz7_R4TransportCircleCoordinates.lean

SHA256 `39bdcb056866b0e8bb6d604a4c369589ff4e6a309e26ccc4d92181cb4ca56bf1`.

```lean
theorem circle_total_coordinates (block : Array U8 32#usize) (row : r0_transcript.CircleRow) :
    ∃ p : circle.SecureCirclePoint,
      sampler.circle_sample block row = ok p ∧ coordinates p = (model block row).1
```

## docs/research/100bit-spend-path-20261013/evidence/lean-literal-circle-density-20261015/import-sources/R0P/CircleSampler.lean

SHA256 `00c6f8cf0999b7d97591aa500bd6d671345963d543a02a0125bfd1eeecbea100`.

```lean
theorem circleSampleParameterWith_rejected (f : Point WideExact) (t : CircleParam)
    (ht : t.im = 0) : circleSampleParameterWith f t = f
```

```lean
theorem circleSampleParameterWith_accepted (f : Point WideExact) (t : CircleParam)
    (ht : t.im ≠ 0) : circleSampleParameterWith f t =
      embedCirclePoint ⟨point t, point_on_circle t (outside_has_denominator t ht)⟩
```

```lean
theorem circleSample0_mass :
    mean (fun s : State => indicator (z0Bad' (circleSample0 s))) ≤
      (1 + deltaQ) / (AspisV8R15.ExactTowerBase.P : ℚ)^4
```

```lean
theorem circleSample1_mass (z0 : Point WideExact) (hz0 : z0 ≠ circleFallback1) :
    mean (fun s : State => indicator (z1Bad z0 (circleSample1 s))) ≤
      (1 + deltaQ) / (AspisV8R15.ExactTowerBase.P : ℚ)^4
```

## evidence/replay-dry5-20261026/RPz4_FallbackBridge.lean

SHA256 `790ca5e22e033aa946f07d515268dfb3b7a7b85c315288475362e09698f272b6`.

```lean
theorem fallback_zero_output :
    transcript.circle_fallback_point 0#usize =
      .ok (fromR72Point (encodePoint (point circleFallbackParameter0)))
```

```lean
theorem fallback_one_output :
    transcript.circle_fallback_point 1#usize =
      .ok (fromR72Point (encodePoint (point circleFallbackParameter1)))
```
