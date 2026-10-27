
#[cfg(test)]
mod SDX_diagnostic {
    #[test]
    fn SDX_four_blocks() {
        let mut p = [0u8; 32]; p[..4].copy_from_slice(&2147483647u32.to_le_bytes());
        let mut p1 = [0u8; 32]; p1[..4].copy_from_slice(&2147483648u32.to_le_bytes());
        for (name, block) in [("P",p),("zero",[0u8;32]),("P+1",p1),("ff",[255u8;32])] {
            let (digits,q) = super::low_base_p_digits(&block);
            println!("SDX {} digits={:?} quotient={}",name,digits,q);
        }
    }
}
