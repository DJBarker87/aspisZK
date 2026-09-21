//! Extraction-only module wiring; the two source modules are copied unchanged.
#![allow(dead_code, unexpected_cfgs)]
pub mod field;
pub mod corelib {
    pub use crate::field;
}
mod r17_structured_g;
