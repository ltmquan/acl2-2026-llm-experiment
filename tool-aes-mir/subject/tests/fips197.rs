use aes_fixslice::{decrypt, encrypt};

fn hex16(s: &str) -> [u8; 16] {
    let mut out = [0u8; 16];
    for i in 0..16 {
        out[i] = u8::from_str_radix(&s[2 * i..2 * i + 2], 16).unwrap();
    }
    out
}

#[test]
fn fips197_c1() {
    let key = hex16("000102030405060708090a0b0c0d0e0f");
    let pt = hex16("00112233445566778899aabbccddeeff");
    let ct = hex16("69c4e0d86a7b0430d8cdb78070b4c55a");
    assert_eq!(encrypt(&key, &pt), ct);
    assert_eq!(decrypt(&key, &ct), pt);
}

#[test]
fn fips197_b() {
    let key = hex16("2b7e151628aed2a6abf7158809cf4f3c");
    let pt = hex16("3243f6a8885a308d313198a2e0370734");
    let ct = hex16("3925841d02dc09fbdc118597196a0b32");
    assert_eq!(encrypt(&key, &pt), ct);
    assert_eq!(decrypt(&key, &ct), pt);
}
