extern crate aspis_core as corelib;
use corelib::{field::{M31,CM31,QM31 as K},state_only_spend_query::StateOnlySpendQueryPowers,
    v6_onefold::gamma_combine_v6_packed_layer0};
#[derive(Debug,PartialEq)]enum Error{Length,Canonical}
mod query_arithmetic;
fn main(){query_arithmetic::r55_controls();}
