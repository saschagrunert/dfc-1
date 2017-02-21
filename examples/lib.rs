extern crate libc;
extern crate dfc;

fn main() {
    /*static buf: &'static str = "This input includes an attack pattern. It might CRASH your machine.";
    static pat1: &'static str = "attack";
    static pat2: &'static str = "crash";
    static pat3: &'static str = "Piolink";
    static pat4: &'static str = "ATTACK";*/
    let buf: &str = "This input includes an attack pattern. It might CRASH your machine.";
    let pat1: &str = "attack";
    let pat2: &str = "crash";
    let pat3: &str = "Piolink";
    let pat4: &str = "ATTACK";
    let buf_ptr: *const u8 = buf.as_ptr();
    let pat1_ptr: *const u8 = pat1.as_ptr();
    let pat2_ptr: *const u8 = pat2.as_ptr();
    let pat3_ptr: *const u8 = pat3.as_ptr();
    let pat4_ptr: *const u8 = pat4.as_ptr();

    unsafe {
        let dfc = dfc::DFC_New();
        dfc::DFC_AddPattern(dfc, pat1_ptr, pat1.len() as isize, false, 0);
        dfc::DFC_AddPattern(dfc, pat2_ptr, pat2.len() as isize, true, 1);
        dfc::DFC_AddPattern(dfc, pat3_ptr, pat3.len() as isize, true, 2);
        dfc::DFC_AddPattern(dfc, pat4_ptr, pat4.len() as isize, true, 3);
        dfc::DFC_FreeStructure(dfc);
    }
}
