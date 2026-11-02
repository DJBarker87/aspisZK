/// Direct call into the standard library shipped with the selected compiler.
/// No native Error payload, ErrorData, or getter is replaced by a copy.
pub fn kind(e: &std::io::Error) -> std::io::ErrorKind { e.kind() }
