// Smallest type/control probe. No OS primitive, provider installation or
// source-to-model association is claimed by this synthetic crate.
pub enum EntropyError { Os(getrandom::Error), RepeatedZeroBlock }
impl From<getrandom::Error> for EntropyError {
    fn from(value: getrandom::Error) -> Self { Self::Os(value) }
}
pub fn wrap(value: getrandom::Error) -> EntropyError { EntropyError::from(value) }
pub fn selected(status: Result<(), getrandom::Error>) -> Result<(), ()> {
    let status = status.map_err(EntropyError::from);
    status.map_err(|_| ())
}
pub fn move_value(value: EntropyError) -> EntropyError { let moved = value; moved }
pub fn copy_error(value: getrandom::Error) -> (getrandom::Error, getrandom::Error) {
    (value, value)
}
pub fn repeated() -> EntropyError { EntropyError::RepeatedZeroBlock }
