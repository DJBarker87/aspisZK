//! Read-only extraction roots; shipped host feature ct-host-prover is explicit.
#![cfg(kani)]
pub fn fibre<E:aspis_core::r0::scalar::CodeField>(u:aspis_core::r0::domain::FibreIndex)->aspis_core::r0::domain::Point<E> {aspis_core::r0::domain::fibre_point(u)}
pub fn trace_clone(t:&aspis_statement::state_only_trace::StateOnlyTraceFoundation)->aspis_statement::state_only_trace::StateOnlyTraceFoundation {t.clone()}
pub fn trace_value(tag:u16,i:usize,x:aspis_core::field::WideExact) {aspis_r1_cost_probe::trace::value(tag,i,x)}
pub fn coefficients<T:Copy>(variant:aspis_r1_cost_probe::transport::Variant,rows:&[T;1024])->[T;1024] {variant.coefficients(rows)}

mod reverse;
pub fn reverse_reference(x:u32)->u32 {reverse::reverse_reference(x)}
