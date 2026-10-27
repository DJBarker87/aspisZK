//! Owned error observation reference. Only the fields consumed by reserve are
//! represented here; this does not give a representation of arbitrary dyn Error.
use std::io::{Error, ErrorKind};
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct OwnedError { pub kind: ErrorKind }
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Observation { pub reserved: bool, pub last_error: Option<ErrorKind> }
pub fn owned_observe(result: Result<bool, OwnedError>) -> Observation {
    match result {
        Ok(reserved) => Observation { reserved, last_error: None },
        Err(error) => Observation { reserved: false, last_error: Some(error.kind) },
    }
}
pub fn native_observe(result: Result<bool, Error>) -> Observation {
    match result {
        Ok(reserved) => Observation { reserved, last_error: None },
        Err(error) => Observation { reserved: false, last_error: Some(error.kind()) },
    }
}
pub fn owned_open_error(error: OwnedError) -> Result<bool, OwnedError> {
    if error.kind == ErrorKind::AlreadyExists { Ok(false) } else { Err(error) }
}
pub fn native_open_error(error: Error) -> Result<bool, Error> {
    if error.kind() == ErrorKind::AlreadyExists { Ok(false) } else { Err(error) }
}
