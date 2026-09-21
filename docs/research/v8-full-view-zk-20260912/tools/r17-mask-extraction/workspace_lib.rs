//! Extraction-only wiring; source modules remain separate and source-pinned.
#![allow(dead_code, unexpected_cfgs)]
pub mod field;
pub mod corelib { pub use crate::field; }
mod r17_structured_g;
mod r17_mask_workspace;
