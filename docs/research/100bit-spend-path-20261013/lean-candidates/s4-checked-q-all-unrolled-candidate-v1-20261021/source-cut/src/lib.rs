pub const P: u32 = 0x7fff_ffff;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Q([u32; 4]);

impl Q {
    // This is copied from the isolated candidate method, whose only change
    // relative to the pinned production method is replacing Iterator::all
    // with these four ordered comparisons.
    pub fn from_limbs(x: [u32; 4]) -> Option<Self> {
        let [a, b, c, d] = x;
        if a < P && b < P && c < P && d < P {
            Some(Self(x))
        } else {
            None
        }
    }

    pub fn limbs(self) -> [u32; 4] { self.0 }
}

pub fn from_limbs_entry(x: [u32; 4]) -> Option<Q> {
    Q::from_limbs(x)
}
