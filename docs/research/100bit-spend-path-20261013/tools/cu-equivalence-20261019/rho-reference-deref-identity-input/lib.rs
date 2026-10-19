// Exact identity-body spelling. Standard method declaration transport is a
// separate obligation; this input is not itself an admitted runtime primitive.
pub fn reborrow<'a,'b,T>(value:&'a mut &'b mut T)->&'a mut T { value }
pub fn view<'a,'b,T>(value:&'a &'b mut T)->&'a T { value }
