// Verbatim decode_k method on a local record carrier. Private-token provenance is NOT proved.
pub(crate) struct XRg_Record<'a> {
    row: u8,
    framed: &'a [u8],
}

impl<'a> XRg_Record<'a> {
    pub(crate) fn row(&self) -> u8 {
        self.row
    }

    pub(crate) fn framed(&self) -> &'a [u8] {
        self.framed
    }

    pub(crate) fn payload(&self) -> &'a [u8] {
        &self.framed[5..]
    }

    /// Decode checked base-field limbs from a semantic record. The
    /// validation token proves the 16-byte high half is zero and the
    /// low K encoding canonical, while this method still checks the
    /// requested range and record class.
    pub(crate) fn decode_k<const N: usize>(
        &self,
        offset_values: usize,
    ) -> Result<[K; N], Error> {
        if self.row < 14 {
            return Err(Error::InvalidRow);
        }
        let byte_offset = offset_values
            .checked_mul(32)
            .ok_or(Error::Length { row: self.row })?;
        let byte_len = N.checked_mul(32).ok_or(Error::Length { row: self.row })?;
        let end = byte_offset
            .checked_add(byte_len)
            .ok_or(Error::Length { row: self.row })?;
        let bytes = self
            .payload()
            .get(byte_offset..end)
            .ok_or(Error::Length { row: self.row })?;
        let mut out = [K::ZERO; N];
        for (value, part) in bytes.chunks_exact(32).enumerate() {
            out[value] = K::from_le_bytes(&part[..16]).ok_or(Error::NonCanonical {
                row: self.row,
                value: offset_values + value,
            })?;
        }
        Ok(out)
    }
}


// claims.rs 47-55 storage stage: decode calls supplied as predecoded Result rows.
// Original record lookup and allocation failure are outside this stage's claim.
fn XRg_claims_storage(rows:[Result<[K;29],Error>;3])->Result<Box<[[K;29];3]>,Error> {
    let mut out=aspis_core::r0::heap::uninit::<[[K;29];3]>().map_err(|_|Error::Allocation)?;
    unsafe {
        for p in 0..3 {
            out.as_mut_ptr().cast::<[K;29]>().add(p).write(rows[p]?);
        }
        Ok(out.assume_init())
    }
}

fn XRg_validate_record_fields(row: u8, payload: &[u8]) -> Result<(), Error> {
    for (value, bytes) in payload.chunks_exact(32).enumerate() {
        let x = aspis_core::field::WideExact::from_le_bytes(bytes).ok_or(Error::NonCanonical { row, value })?;
        if x.c1() != K::ZERO {
            return Err(Error::NonCanonical { row, value });
        }
    }
    Ok(())
}

fn XRg_semantic_boundary(polynomial: &[K; 28]) -> K {
        let boundary = polynomial.iter().copied().fold(polynomial[0], K::add);
    boundary
}

// Dot::push loop projection after Q::raw; the private Q/raw relation stays OPEN.
struct XRg_Dot { sums:[u64;4] }
impl XRg_Dot {
    fn push_raw(&mut self,raw:[u64;4]) {
        const P:u32=2147483647;
            for j in 0..4 {
                self.sums[j]=self.sums[j].wrapping_add(
                    (raw[j]&u64::from(P)).wrapping_add(raw[j]>>31u32));
            }

    }
}

// Exact circle_sample fallback closure body; successful sample branch excluded.
fn XRg_circle_fallback(row:aspis_r1_cost_probe::sampler::CircleRow,error:aspis_core::circle::CirclePointError)->aspis_core::circle::SecureCirclePoint {
    use aspis_r1_cost_probe::sampler::CircleRow;
    let fallback=|_| {
        aspis_core::transcript::circle_fallback_point(match row {
            CircleRow::First=>0,
            CircleRow::Second=>1,
        })
    };
    fallback(error)
}
