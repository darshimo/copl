static mut N: u32 = 0;

pub fn get_id() -> u32 {
    let mut ret = 0;

    unsafe {
        ret = N;
        N += 1;
    };

    ret
}
