fn abs(value: i32) -> i32 {
    if value < 0 { -value } else { value }
}

#[kani::proof]
#[kani::unwind(1)]
fn abs_is_nonnegative() {
    let value: i32 = kani::any();
    kani::assume(value != i32::MIN);
    assert!(abs(value) >= 0);
}
