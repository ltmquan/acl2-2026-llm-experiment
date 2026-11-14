// Transcription of the RAR code of Section 5.1 (struct, free_head, used_head) and Figures 5-6
// (aset_add, aset_del_head, aset_del) of hardin-arrayset, used by grade.sh for R1.
// Compared token by token (whitespace and // comments ignored, `pub` dropped) with /work/src/arrayset.rs.
// ARR_SZ: the paper writes `const ARR_SZ: uint = 1024;` (`uint` is not a Rust type); the grader accepts
// any type there (see NOTES.md) and checks only that the value is 1024.

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

fn aset_add(val: i64, mut aset: Arrayset) -> Arrayset {
  let mut idx: usize = ARR_SZ;

    aset = aset_transfer(false, aset);                     // false => free head to used head

    if (aset.err == 1) {      // no error
      aset.avals[aset.anext[aset.used_lst]] = val;
    }

    return aset;
}

fn aset_del_head(mut aset: Arrayset) -> Arrayset {
  let idx: usize;

    aset = aset_transfer(true, aset);             // true => used head to free head

    return aset;
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
