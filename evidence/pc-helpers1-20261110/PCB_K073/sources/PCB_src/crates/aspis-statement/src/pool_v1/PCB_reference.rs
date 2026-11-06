#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct Location {pub page_number:u64,pub slot:u16}
pub fn location(sequence:u64)->Location {
    Location {page_number:sequence/256, slot:(sequence%256) as u16}
}
