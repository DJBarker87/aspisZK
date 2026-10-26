//! All OS result values are harness inputs; no syscall stubs are present.
use aspis_core::field::{M31, CM31, QM31, WideExact};
use aspis_r1_cost_probe::transport::Variant;

fn variant() -> Variant {
    let tag:u8 = kani::any();
    kani::assume(tag < 3);
    match tag { 0 => Variant::S1, 1 => Variant::S2, _ => Variant::D }
}

fn m31_rows() -> [M31; 1024] {
    let bits: [u32; 1024] = kani::any();
    let mut rows = [M31::ZERO; 1024];
    let mut i = 0;
    while i < 1024 { rows[i] = M31(bits[i]); i += 1; }
    rows
}
fn qm31_rows() -> [QM31; 1024] {
    let bits: [[u32;4]; 1024] = kani::any();
    let mut rows = [QM31::ZERO; 1024];
    let mut i = 0;
    while i < 1024 {
        rows[i] = QM31 { c0:CM31 { a:M31(bits[i][0]), b:M31(bits[i][1]) },
            c1:CM31 { a:M31(bits[i][2]), b:M31(bits[i][3]) } };
        i += 1;
    }
    rows
}
fn wide_rows() -> [WideExact; 1024] {
    let bits: [[u32;8]; 1024] = kani::any();
    let mut rows = [WideExact::ZERO; 1024];
    let mut i = 0;
    while i < 1024 {
        // Every valid WideExact can be selected; invalid limb words map to zero.
        rows[i] = WideExact::from_limbs(bits[i]).unwrap_or(WideExact::ZERO);
        i += 1;
    }
    rows
}

#[kani::proof]
#[kani::unwind(1026)]
pub fn coefficients_m31() {
    let rows = m31_rows(); let variant = variant();
    let position:usize = kani::any(); kani::assume(position < 1024);
    let native = variant.coefficients(&rows);
    let reference = super::coefficients::owned(variant, &rows);
    assert!(native[position].0 == reference[position].0);
}
#[kani::proof]
#[kani::unwind(1026)]
pub fn coefficients_qm31() {
    let rows = qm31_rows(); let variant = variant();
    let position:usize = kani::any(); kani::assume(position < 1024);
    let native = variant.coefficients(&rows);
    let reference = super::coefficients::owned(variant, &rows);
    assert!(native[position] == reference[position]);
}
#[kani::proof]
#[kani::unwind(1026)]
pub fn coefficients_wide() {
    let rows = wide_rows(); let variant = variant();
    let position:usize = kani::any(); kani::assume(position < 1024);
    let native = variant.coefficients(&rows);
    let reference = super::coefficients::owned(variant, &rows);
    assert!(native[position].to_limbs() == reference[position].to_limbs());
}
#[kani::proof]
#[kani::unwind(1026)]
pub fn from_fn_m31() {
    let rows = m31_rows();
    let position:usize = kani::any(); kani::assume(position < 1024);
    let native:[M31;1024] = std::array::from_fn(|i| rows[i]);
    let reference = super::coefficients::copy_owned(&rows);
    assert!(native[position].0 == reference[position].0);
}
#[kani::proof]
#[kani::unwind(1026)]
pub fn from_fn_qm31() {
    let rows = qm31_rows();
    let position:usize = kani::any(); kani::assume(position < 1024);
    let native:[QM31;1024] = std::array::from_fn(|i| rows[i]);
    let reference = super::coefficients::copy_owned(&rows);
    assert!(native[position] == reference[position]);
}
#[kani::proof]
#[kani::unwind(1026)]
pub fn from_fn_wide() {
    let rows = wide_rows();
    let position:usize = kani::any(); kani::assume(position < 1024);
    let native:[WideExact;1024] = std::array::from_fn(|i| rows[i]);
    let reference = super::coefficients::copy_owned(&rows);
    assert!(native[position].to_limbs() == reference[position].to_limbs());
}

#[kani::proof]
#[kani::unwind(4)]
pub fn error_os_projection_retains_code() {
    let code:i32 = kani::any();
    let native = std::io::Error::from_raw_os_error(code);
    assert!(native.raw_os_error() == Some(code));
    assert!((native.kind() == std::io::ErrorKind::AlreadyExists) ==
        super::world::retry_collision(code));
}

#[kani::proof]
#[kani::unwind(4)]
pub fn error_result_reserve_branch() {
    let code:i32 = kani::any(); let success:bool = kani::any();
    let native:Result<bool,std::io::Error> =
        if success { Ok(true) } else { Err(std::io::Error::from_raw_os_error(code)) };
    let observed = match native {
        Ok(b) => (b, None),
        Err(e) if e.kind() == std::io::ErrorKind::AlreadyExists => (false,None),
        Err(e) => (false,e.raw_os_error()),
    };
    let reference = if success { (true,None) }
        else if super::world::retry_collision(code) { (false,None) }
        else { (false,Some(code)) };
    assert!(observed == reference);
}

struct Sink { bytes:[u8;4], length:usize, fail:bool, calls:usize, frame:u64 }
impl std::fmt::Write for Sink {
    fn write_str(&mut self, s:&str) -> std::fmt::Result {
        assert!(s.as_bytes() == &self.bytes[..self.length]);
        self.calls += 1;
        if self.fail { Err(std::fmt::Error) } else { Ok(()) }
    }
}
fn formatter_write(two:bool) {
    use std::fmt::{Formatter,FormattingOptions};
    let mut bytes:[u8;4] = kani::any();
    for b in &mut bytes { *b &= 0x7f; }
    let length:usize = kani::any(); kani::assume(length <= 4);
    let text = std::str::from_utf8(&bytes[..length]).unwrap();
    let frame:u64 = kani::any(); let fail:bool = kani::any();
    let mut sink = Sink {bytes,length,fail,calls:0,frame};
    let mut options = FormattingOptions::new();
    options.width(kani::any::<Option<u16>>()).precision(kani::any::<Option<u16>>())
        .alternate(kani::any()).sign_aware_zero_pad(kani::any()).fill(kani::any::<char>());
    {
        let mut formatter = Formatter::new(&mut sink,options);
        assert!(formatter.write_str(text).is_err() == fail);
        if two { assert!(formatter.write_str(text).is_err() == fail); }
        assert!(formatter.options() == options);
    }
    assert!(sink.calls == if two {2} else {1});
    assert!(sink.frame == frame);
}
#[kani::proof]
#[kani::unwind(6)]
pub fn formatter_write_safe_quotient() { formatter_write(false); }
#[kani::proof]
#[kani::unwind(6)]
pub fn formatter_two_writes_shared_sink() { formatter_write(true); }
