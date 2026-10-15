    /// Decode eight base-P digits without reduction; rejects any digit >= P.
    /// This is `digitsField`, not the natural-number cast of a base-P rank.
    #[inline(always)]
    pub fn from_limbs(limbs: [u32; Self::LIMB_COUNT]) -> Option<Self> {
        if limbs[0] >= P || limbs[1] >= P || limbs[2] >= P || limbs[3] >= P
            || limbs[4] >= P || limbs[5] >= P || limbs[6] >= P || limbs[7] >= P {
            return None;
        }
        let [a, b, c, d, e, f, g, h] = limbs;
        Some(Self {
            c0: QM31 {
                c0: CM31 {
                    a: M31(a),
                    b: M31(b),
                },
                c1: CM31 {
                    a: M31(c),
                    b: M31(d),
                },
            },
            c1: QM31 {
                c0: CM31 {
                    a: M31(e),
                    b: M31(f),
                },
                c1: CM31 {
                    a: M31(g),
                    b: M31(h),
                },
            },
        })
    }