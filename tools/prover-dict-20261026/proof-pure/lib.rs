//! Extraction entrypoints only. These wrappers are absent from shipped Cargo.
#[cfg(kani)]
pub fn wide_c0(x:aspis_core::field::WideExact)->aspis_core::field::QM31 { x.c0() }
#[cfg(kani)]
pub fn wide_c1(x:aspis_core::field::WideExact)->aspis_core::field::QM31 { x.c1() }
#[cfg(kani)]
pub fn wide_clone(x:&aspis_core::field::WideExact)->aspis_core::field::WideExact { x.clone() }
#[cfg(kani)]
pub fn wide_eq(x:&aspis_core::field::WideExact,y:&aspis_core::field::WideExact)->bool { x==y }
#[cfg(kani)]
pub fn secure_circle_eq(x:&aspis_core::circle::SecureCirclePoint,y:&aspis_core::circle::SecureCirclePoint)->bool { x==y }
#[cfg(kani)]
pub fn leaf_bits()->u32 { aspis_r1_cost_probe::multiproof::LEAF_BITS }
#[cfg(kani)]
pub fn max_batch()->usize { aspis_r1_cost_probe::multiproof::MAX_BATCH }
#[cfg(kani)]
pub fn lanes()->usize { aspis_r1_cost_probe::r1_wire::LANES }
#[cfg(kani)]
pub fn claims()->usize { aspis_r1_cost_probe::r1_wire::CLAIMS }
#[cfg(kani)]
pub fn domain()->&'static [u8] { aspis_r1_cost_probe::r1_wire::DOMAIN }
#[cfg(kani)]
pub fn cm31_new(a:aspis_core::field::M31,b:aspis_core::field::M31)->aspis_core::field::CM31 { aspis_core::field::CM31::new(a,b) }
#[cfg(kani)]
pub fn wide_to_limbs(x:aspis_core::field::WideExact)->[u32;8] { x.to_limbs() }
#[cfg(kani)]
pub fn wide_to_bytes(x:aspis_core::field::WideExact)->[u8;32] { x.to_le_bytes() }
#[cfg(kani)]
pub fn wide_from_bytes(x:&[u8])->Option<aspis_core::field::WideExact> { aspis_core::field::WideExact::from_le_bytes(x) }
