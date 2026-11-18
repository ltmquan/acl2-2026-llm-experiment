// Restricted Algorithmic Rust (RAR) array-backed set (multiset).
//
// The code between the "RAR begin" and "RAR end" delimiters is the RAR
// program; it is transpiled to RAC (Restricted Algorithmic C) by the
// transpiler in /work/plexi, and from there to ACL2 by the RAC translator.
// The code outside the delimiters is ordinary Rust (a test driver).

#![allow(unused_parens)]
#![allow(unused_variables)]
#![allow(unused_assignments)]
#![allow(unused_mut)]
#![allow(dead_code)]
#![allow(non_snake_case)]
#![allow(redundant_semicolons)]

// The C-like for loop used by RAR:
//   cfor!(init; test; update; { body });
macro_rules! cfor {
    ($init:stmt; $test:expr; $update:expr; $body:block) => {{
        $init;
        while $test {
            $body;
            $update;
        }
    }};
}

// RAR begin

const ARR_SZ: usize = 1024;              // Can be sized up to billions

#[derive(Copy, Clone)]
struct Arrayset {
  anext: [usize; ARR_SZ],
  avals: [i64; ARR_SZ],
  free_lst: usize,
  used_lst: usize,
  err: usize,
}

fn free_head(aset: Arrayset) -> usize {
  let mut retval: usize = ARR_SZ;
  if (aset.free_lst < ARR_SZ) {
    retval = aset.anext[aset.free_lst];
  }
  return retval;
}

fn used_head(aset: Arrayset) -> usize {
  let mut retval: usize = ARR_SZ;
  if (aset.used_lst < ARR_SZ) {
    retval = aset.anext[aset.used_lst];
  }
  return retval;
}

// Initialize: element 0 is unused (anext[0] = 0); elements 1 .. ARR_SZ-1
// form a circular free list whose last element (free_lst) is ARR_SZ-1; the
// used list is empty (used_lst = ARR_SZ).  Requires ARR_SZ >= 2.
fn aset_init(mut aset: Arrayset) -> Arrayset {
  cfor!(let mut i: usize = 0; i < ARR_SZ; i += 1; {
    aset.avals[i] = 0;
    if (i == 0) {
      aset.anext[i] = 0;
    } else if (i == ARR_SZ - 1) {
      aset.anext[i] = 1;
    } else {
      aset.anext[i] = i + 1;
    }
  });
  aset.free_lst = ARR_SZ - 1;
  aset.used_lst = ARR_SZ;
  aset.err = 1;
  return aset;
}

// Move the head element of one circular list to the head of the other.
// used_to_free == true  => used head to free head
// used_to_free == false => free head to used head
// On success err is set to 1; if the source list is empty, err is set to
// ARR_SZ and the lists are unchanged.
fn aset_transfer(used_to_free: bool, mut aset: Arrayset) -> Arrayset {
  let mut src: usize = aset.free_lst;
  let mut dst: usize = aset.used_lst;
  if (used_to_free) {
    src = aset.used_lst;
    dst = aset.free_lst;
  }
  if (src < ARR_SZ) {
    let hd: usize = aset.anext[src];
    // Unlink hd from the source list.
    if (hd == src) {
      src = ARR_SZ;                        // source list becomes empty
    } else {
      aset.anext[src] = aset.anext[hd];
    }
    // Link hd in at the head of the destination list.
    if (dst < ARR_SZ) {
      aset.anext[hd] = aset.anext[dst];
      aset.anext[dst] = hd;
    } else {
      aset.anext[hd] = hd;                 // destination was empty
      dst = hd;
    }
    if (used_to_free) {
      aset.used_lst = src;
      aset.free_lst = dst;
    } else {
      aset.free_lst = src;
      aset.used_lst = dst;
    }
    aset.err = 1;
  } else {
    aset.err = ARR_SZ;
  }
  return aset;
}

fn aset_add(val: i64, mut aset: Arrayset) -> Arrayset {
  let mut idx: usize = ARR_SZ;

  aset = aset_transfer(false, aset);       // false => free head to used head

  if (aset.err == 1) {      // no error
    aset.avals[aset.anext[aset.used_lst]] = val;
  }

  return aset;
}

fn aset_del_head(mut aset: Arrayset) -> Arrayset {
  let idx: usize;

  aset = aset_transfer(true, aset);        // true => used head to free head

  return aset;
}

// Search the circular list containing start, beginning with the element
// after start, for an element with value val.  Returns the index previ of
// the predecessor of that element (so that avals[anext[previ]] == val), or
// ARR_SZ if there is none.
fn aset_find_val_from(start: usize, val: i64, aset: Arrayset) -> usize {
  let mut retval: usize = ARR_SZ;
  let mut idx: usize = start;
  let mut done: bool = !(start < ARR_SZ);
  cfor!(let mut i: usize = 0; (i < ARR_SZ) && !done; i += 1; {
    let nxt: usize = aset.anext[idx];
    if (aset.avals[nxt] == val) {
      retval = idx;
      done = true;
    } else if (nxt == start) {
      done = true;
    } else {
      idx = nxt;
    }
  });
  return retval;
}

fn aset_del(val: i64, mut aset: Arrayset) -> Arrayset {
  let mut prev_index: usize = ARR_SZ;

  if (aset.used_lst < ARR_SZ) {
    prev_index = aset_find_val_from(aset.used_lst, val, aset);

    if ((prev_index < ARR_SZ) && (prev_index != aset.free_lst)) {

      // Rotate used pointer
      aset.used_lst = prev_index;

      aset = aset_del_head(aset);
    } else {
      aset.err = ARR_SZ;
    }
  } else {
    aset.err = ARR_SZ;
  }
  return aset;
}

// RAR end

// ---------------------------------------------------------------------
// Test driver (not part of the RAR program).
// ---------------------------------------------------------------------

fn empty_aset() -> Arrayset {
    Arrayset { anext: [0; ARR_SZ], avals: [0; ARR_SZ], free_lst: 0, used_lst: 0, err: 0 }
}

fn used_list(aset: &Arrayset) -> Vec<i64> {
    let mut v = Vec::new();
    if aset.used_lst < ARR_SZ {
        let mut i = aset.anext[aset.used_lst];
        loop {
            v.push(aset.avals[i]);
            if i == aset.used_lst { break; }
            i = aset.anext[i];
        }
    }
    v
}

fn main() {
    let mut a = aset_init(empty_aset());
    assert!(a.err == 1 && a.used_lst == ARR_SZ && a.free_lst == ARR_SZ - 1);
    a = aset_add(22, a);
    a = aset_add(33, a);
    a = aset_add(-7, a);
    assert!(used_list(&a) == vec![-7, 33, 22]);
    a = aset_del(33, a);
    assert!(a.err == 1);
    assert!(a.avals[free_head(a)] == 33);
    assert!(used_list(&a).len() == 2);
    a = aset_del(99, a);
    assert!(a.err == ARR_SZ);
    a = aset_del_head(a);
    a = aset_del_head(a);
    assert!(a.err == 1 && a.used_lst == ARR_SZ);
    a = aset_del_head(a);
    assert!(a.err == ARR_SZ);
    // Fill completely, then one more add fails.
    let mut k: i64 = 0;
    while k < (ARR_SZ as i64) - 1 { a = aset_add(k, a); assert!(a.err == 1); k += 1; }
    assert!(a.free_lst == ARR_SZ);
    a = aset_add(5, a);
    assert!(a.err == ARR_SZ);
    println!("arrayset tests passed");
}
