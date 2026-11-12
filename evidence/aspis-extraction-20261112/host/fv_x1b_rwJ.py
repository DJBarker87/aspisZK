#!/usr/bin/env python3
"""X1b item J: every `Option::ok_or` site of the on-chain emission (30 sites in 18 functions) in an explicit form,
`match o { Some(v) => v, None => return Err(e) }` or `let Some(x) = o else { return Err(e) }`, the same error value
at the same point. `?` on these sites converts through `From<E> for E`, the identity, so `return Err(e)` is what the
frozen code does. Line- and column-preserving: no line is added or removed, and the text before every expression that
can panic keeps its column (a `match` keyword is put into the indentation, or at the end of the previous line with
the old `let x =` replaced by spaces). Sites not in the on-chain emission (test oracles, the two-transaction
functions, the lifecycle handlers compiled out by item D) are not touched.
usage: fv_x1b_rwJ.py <tree>   (edits the tree in place; refuses the frozen tree)"""
import sys
from pathlib import Path
T = Path(sys.argv[1]); assert 'src-frz-a' not in str(T)

def sub(path, old, new, after=None, count=1):
    p = T / path; t = p.read_text()
    start = t.index(after) if after else 0
    head, tail = t[:start], t[start:]
    assert tail.count(old) >= count and (after or t.count(old) == count), (path, old, t.count(old))
    tail = tail.replace(old, new, count)
    assert len(new.split('\n')) == len(old.split('\n')), ('line count', path, old)
    p.write_text(head + tail)

SP = lambda s: ' ' * len(s)

# aspis-core (prover-compiled crate)
sub('crates/aspis-core/src/circle.rs',
    '''    let inverse_denominator = QM31::ONE
        .add(square)
        .try_inv()
        .ok_or(CirclePointError::SingularParameter)?;''',
    '''    let inverse_denominator = match QM31::ONE
        .add(square)
        .try_inv()
        { Some(v) => v, None => return Err(CirclePointError::SingularParameter) };''')

# aspis-statement
for k in range(0, 32, 4):
    sub('crates/aspis-statement/src/atomic_statement.rs',
        '''        M31::from_le_bytes([bytes[%d], bytes[%d], bytes[%d], bytes[%d]])
            .ok_or(AtomicStatementError::NonCanonicalDigest)?,''' % (k, k + 1, k + 2, k + 3),
        '''  match M31::from_le_bytes([bytes[%d], bytes[%d], bytes[%d], bytes[%d]])
            { Some(v) => v, None => return Err(AtomicStatementError::NonCanonicalDigest) },''' % (k, k + 1, k + 2, k + 3))

# aspis-r1-cost-probe
sub('crates/aspis-r1-cost-probe/src/verifier.rs',
    '{let x=E::from_le_bytes(c).ok_or(Error::Parse)?;if k&&',
    '{let Some(x)=E::from_le_bytes(c) else {return Err(Error::Parse)};if k&&')
sub('crates/aspis-r1-cost-probe/src/compact.rs',
    '        QM31::from_le_bytes(c).ok_or(CodecError::NonCanonical)?;',
    '  match QM31::from_le_bytes(c) { Some(_) => {} None => return Err(CodecError::NonCanonical) }')
sub('crates/aspis-r1-cost-probe/src/compact.rs',
    '        let size = row_shape(row).ok_or(CodecError::Length)?.1;\n        out[dst..dst + 5]',
    '        let Some((_, size)) = row_shape(row) else { return Err(CodecError::Length) };\n        out[dst..dst + 5]')
sub('crates/aspis-r1-cost-probe/src/candidate.rs',
    '''    for l in 0..26 {
        M31::from_le_bytes(q[s * 120 + l * 4..s * 120 + l * 4 + 4].try_into().unwrap()).ok_or(Error::Parse)?;
    }
    Ok(())''',
    '''    for l in 0..26 {
  match M31::from_le_bytes(q[s * 120 + l * 4..s * 120 + l * 4 + 4].try_into().unwrap()) { Some(_) => {} None => return Err(Error::Parse) }
    }
    Ok(())''')
sub('crates/aspis-r1-cost-probe/src/candidate.rs',
    '''    scan_slot_base(q, s)?;
    K::from_le_bytes(&q[s * 120 + 104..s * 120 + 120]).ok_or(Error::Parse)?;
    K::from_le_bytes(&q[480 + s * 32..480 + s * 32 + 16]).ok_or(Error::Parse)?;
    K::from_le_bytes(&q[480 + s * 32 + 16..480 + s * 32 + 32]).ok_or(Error::Parse)?;''',
    '''    scan_slot_base(q, s)?; match
    K::from_le_bytes(&q[s * 120 + 104..s * 120 + 120]) { Some(_) => {} None => return Err(Error::Parse) } match
    K::from_le_bytes(&q[480 + s * 32..480 + s * 32 + 16]) { Some(_) => {} None => return Err(Error::Parse) } match
    K::from_le_bytes(&q[480 + s * 32 + 16..480 + s * 32 + 32]) { Some(_) => {} None => return Err(Error::Parse) }''')
sub('crates/aspis-r1-cost-probe/src/candidate.rs',
    '''        y1,
        inactive: E::from_le_bytes(&proof[compact::OFF_INACTIVE..compact::OFF_ROUND0]).ok_or(Error::Parse)?,''',
    '''        y1, inactive:
        match     E::from_le_bytes(&proof[compact::OFF_INACTIVE..compact::OFF_ROUND0]) { Some(v) => v, None => return Err(Error::Parse) },''')
sub('crates/aspis-r1-cost-probe/src/one_tx.rs',
    '''fn relation_view(proof: &[u8]) -> Result<View<'_>, Error> {
    let inactive = E::from_le_bytes(&proof[compact::OFF_INACTIVE..compact::OFF_ROUND0]).ok_or(Error::Parse)?;''',
    '''fn relation_view(proof: &[u8]) -> Result<View<'_>, Error> { let inactive = match
''' + SP('    let inactive = ') + '''E::from_le_bytes(&proof[compact::OFF_INACTIVE..compact::OFF_ROUND0]) { Some(v) => v, None => return Err(Error::Parse) };''')
sub('crates/aspis-r1-cost-probe/src/one_tx.rs',
    '''        let bytes = &certificate[64 * b..64 * b + 64];
        let c0 = E::from_le_bytes(&bytes[..32]).ok_or(Error::Parse)?;
        let c2 = E::from_le_bytes(&bytes[32..]).ok_or(Error::Parse)?;''',
    '''        let bytes = &certificate[64 * b..64 * b + 64]; let c0 = match
''' + SP('        let c0 = ') + '''E::from_le_bytes(&bytes[..32]) { Some(v) => v, None => return Err(Error::Parse) }; let c2 = match
''' + SP('        let c2 = ') + '''E::from_le_bytes(&bytes[32..]) { Some(v) => v, None => return Err(Error::Parse) };''')
sub('crates/aspis-r1-cost-probe/src/r1_wire.rs',
    '''fn validate_record_fields(row: u8, payload: &[u8]) -> Result<(), Error> {
    for (value, bytes) in payload.chunks_exact(32).enumerate() {
        let x = WideExact::from_le_bytes(bytes).ok_or(Error::NonCanonical { row, value })?;''',
    '''fn validate_record_fields(row: u8, payload: &[u8]) -> Result<(), Error> {
    for (value, bytes) in payload.chunks_exact(32).enumerate() { let x = match
''' + SP('        let x = ') + '''WideExact::from_le_bytes(bytes) { Some(v) => v, None => return Err(Error::NonCanonical { row, value }) };''')
sub('crates/aspis-r1-cost-probe/src/r1_wire.rs',
    '''pub fn parse_record(row: u8, record: &[u8]) -> Result<&[u8], Error> {
    let (tag, size) = row_shape(row).ok_or(Error::InvalidRow)?;''',
    '''pub fn parse_record(row: u8, record: &[u8]) -> Result<&[u8], Error> { let (tag, size) = match
''' + SP('    let (tag, size) = ') + '''row_shape(row) { Some(v) => v, None => return Err(Error::InvalidRow) };''')
# decode_k: the definition compiled on chain is the second one (frozen r1_wire.rs 271), after the E3 comment's function
DK = '''        let byte_offset = offset_values
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
        let mut out = [QM31::ZERO; N];
        // FUTURE-VERSION EXPERIMENT E3'''
DKN = '''        let byte_offset = match offset_values
            .checked_mul(32)
            { Some(v) => v, None => return Err(Error::Length { row: self.row }) };
        let Some(byte_len) = N.checked_mul(32) else { return Err(Error::Length { row: self.row }) };
        let end = match byte_offset
            .checked_add(byte_len)
            { Some(v) => v, None => return Err(Error::Length { row: self.row }) };
        let bytes = match self
            .payload()
            .get(byte_offset..end)
            { Some(v) => v, None => return Err(Error::Length { row: self.row }) };
        let mut out = [QM31::ZERO; N];
        // FUTURE-VERSION EXPERIMENT E3'''
sub('crates/aspis-r1-cost-probe/src/r1_wire.rs', DK, DKN)
sub('crates/aspis-r1-cost-probe/src/r1_wire.rs',
    '''    let framed = bytes
        .get(offset..offset + length)
        .ok_or(Error::Length { row })?;
    parse_record(row, framed)?;''',
    '''    let framed = match bytes
        .get(offset..offset + length)
        { Some(v) => v, None => return Err(Error::Length { row }) };
    parse_record(row, framed)?;''')

# program crate (one-transaction definitions only)
sub('programs/r1-cost-probe/src/r1_pool_adapter.rs',
    '''    let expected_body = POOL_V1_PAIR_VERIFIED_AFTERSTATE_BYTES
        .checked_add(proof_length)
        .ok_or(ProgramError::InvalidAccountData)?;''',
    '''    let expected_body = match POOL_V1_PAIR_VERIFIED_AFTERSTATE_BYTES
        .checked_add(proof_length)
        { Some(v) => v, None => return Err(ProgramError::InvalidAccountData) };''',
    after='// Aspis: the one-transaction entry reads the Aspis proof format.')
sub('programs/r1-cost-probe/src/r1_pool_adapter_owned.rs',
    '''    )?;
    let proof_account = accounts.first().ok_or(ProgramError::NotEnoughAccountKeys)?;
    let scanned = scan_proof_buffer(proof_account.data()?)?;''',
    '''    )?; let proof_account = match
''' + SP('    let proof_account = ') + '''accounts.first() { Some(v) => v, None => return Err(ProgramError::NotEnoughAccountKeys) };
    let scanned = scan_proof_buffer(proof_account.data()?)?;''')
sub('programs/r1-cost-probe/src/r1_pool_adapter_owned.rs',
    '''    let proof_end = proof_start.checked_add(validated.proof_length)
        .ok_or(ProgramError::InvalidAccountData)?;''',
    '''    let proof_end = match proof_start.checked_add(validated.proof_length)
        { Some(v) => v, None => return Err(ProgramError::InvalidAccountData) };''',
    after='/// Aspis new gate (replaces the pinned `stage2_owned`')
print('ok')
