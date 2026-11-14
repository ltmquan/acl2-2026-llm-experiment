# Adaptation of `src/soft/fixslice32.rs` (RustCrypto `aes` 0.9.1)

`src/lib.rs` is an AES-128-only adaptation of the crate's 32-bit fixsliced
implementation, in the manner of Section 4.2 of the paper: the round operations
and the key schedule are kept as upstream wrote them, the `cipher`-crate types
are replaced by byte arrays, and single-block `encrypt`/`decrypt` entry points
are added.

* Pristine upstream file: `fixslice32.upstream.rs` (extracted unchanged from
  `/opt/inputs/aes-0.9.1.crate`, `aes-0.9.1/src/soft/fixslice32.rs`).
* The adaptation is produced mechanically from it by `../scripts/adapt.py`
  (`python3 ../scripts/adapt.py fixslice32.upstream.rs src/lib.rs`).
* `../scripts/audit.py fixslice32.upstream.rs src/lib.rs` is a
  whitespace- and comment-insensitive, item-by-item comparison; its output is
  committed as `AUDIT.txt`.  It reports 25 items identical, 11 changed,
  12 removed, and 5 added, all accounted for below.

## Items identical to upstream (25)

`FixsliceKeys128`, `State`, `inv_sub_bytes`, `sub_bytes`, `sub_bytes_nots`, the
`define_mix_columns!` macro and its `mix_columns_0`/`inv_mix_columns_0` and
`mix_columns_1`/`inv_mix_columns_1` instances, `delta_swap_1`, `delta_swap_2`,
`shift_rows_2`, `shift_rows_3`, `inv_shift_rows_1`, `inv_shift_rows_2`,
`xor_columns`, `bitslice`, `memshift32`, `add_round_key`,
`add_round_constant_bit`, `ror`, `ror_distance`, `rotate_rows_1`,
`rotate_rows_2`, `rotate_rows_and_columns_1_1`, `rotate_rows_and_columns_2_2`.

All thirteen of upstream's `debug_assert!`/`debug_assert_eq!` uses in these
functions are kept (they appear in the MIR as checks the interpreter runs).

## Every difference from upstream

### Packaging

1. The file is the root of its own cargo crate (`Cargo.toml`, package
   `aes_fixslice`, edition 2024 as upstream, no dependencies) instead of the
   module `soft::fixslice` of the `aes` crate.  Its inner attribute
   `#![allow(clippy::unreadable_literal)]` therefore applies to the crate.
   `tests/fips197.rs` (FIPS-197 C.1 and B vectors, both directions) is added
   as a cargo integration test.

### Types: byte arrays instead of the `cipher` crate's

2. Removed `use crate::Block;` and `use cipher::{array::Array, consts::U2};`.
3. Added `pub type Block = [u8; 16];` in place of the crate root's
   `pub type Block = Array<u8, U16>;`.
4. Removed `pub(crate) type FixsliceBlocks = U2;`.
5. Changed `pub(crate) type BatchBlocks = Array<Block, FixsliceBlocks>;` to
   `pub(crate) type BatchBlocks = [Block; 2];` (doc comment reworded:
   "AES block batch: two blocks").
6. In `inv_bitslice`, the `default()` initializer
   `let mut output = BatchBlocks::default();` is written out as
   `let mut output: BatchBlocks = [[0u8; 16]; 2];` (`[[u8; 16]; 2]` has no
   `Default` that names `BatchBlocks`; the value is the same, all zeros).
   The rest of `inv_bitslice` is identical.

### Dropped scope: AES-192 and AES-256

7. Removed `FixsliceKeys192`, `FixsliceKeys256`, `aes192_key_schedule`,
   `aes256_key_schedule`, `aes192_decrypt`, `aes192_encrypt`, `aes256_decrypt`,
   `aes256_encrypt`.

### Dropped scope: the untaken `cfg` path (`aes_backend_soft = "compact"`)

The build configuration is the default one (`aes_backend_soft` unset), so the
`#[cfg(not(aes_backend_soft = "compact"))]` code is the code upstream compiles.

8. `aes128_key_schedule`: removed the `#[cfg(aes_backend_soft = "compact")]`
   block (`for i in (8..88).step_by(16) { inv_shift_rows_1(...) }`) and
   unwrapped the `#[cfg(not(...))]` block, keeping its statements verbatim
   (re-indented one level).
9. `aes128_decrypt`: unwrapped the `#[cfg(not(...))]` block around the first
   `inv_shift_rows_2(&mut state);` and the one around the third and fourth
   round bodies inside the loop; removed the `#[cfg(aes_backend_soft =
   "compact")]` block (`inv_shift_rows_2`) at the top of the loop.
10. `aes128_encrypt`: removed the `#[cfg(aes_backend_soft = "compact")]` block
    (`shift_rows_2`) inside the loop; unwrapped the `#[cfg(not(...))]` block
    around the second and third round bodies inside the loop and the one around
    the final `shift_rows_2(&mut state);`.
11. Removed the `cfg` attributes (keeping the items) on
    `define_mix_columns!(mix_columns_2, ...)`,
    `define_mix_columns!(mix_columns_3, ...)`, `inv_shift_rows_3`,
    `rotate_rows_and_columns_1_2`, `rotate_rows_and_columns_1_3`
    (`#[cfg(not(aes_backend_soft = "compact"))]`), and `shift_rows_1`
    (`#[cfg(any(not(aes_backend_soft = "compact"), feature = "hazmat"))]`).

Apart from these `cfg` removals and the re-indentation, the bodies of
`aes128_key_schedule`, `aes128_decrypt`, and `aes128_encrypt`, including their
signatures, are statement-identical to upstream (see `AUDIT.txt`).

### Dropped scope: the `hazmat` module

12. Removed `#[cfg(feature = "hazmat")] pub(crate) mod hazmat { ... }`
    (the feature-gated raw round-function API, not used by the cipher).

### Added single-block entry points

These replace the `cipher`-crate trait implementations in upstream's
`src/soft.rs`, which build a batch from the block, call the two-lane function,
and return lane 0.  Here the block is duplicated into both lanes.

13. `pub fn encrypt_block(rkeys: &FixsliceKeys128, block: &Block) -> Block`
    — `aes128_encrypt` on `[*block, *block]`, returning lane 0.
14. `pub fn decrypt_block(rkeys: &FixsliceKeys128, block: &Block) -> Block`
    — `aes128_decrypt` likewise.
15. `pub fn encrypt(key: &[u8; 16], block: &Block) -> Block` —
    `aes128_key_schedule(key)` then `encrypt_block`.
16. `pub fn decrypt(key: &[u8; 16], block: &Block) -> Block` —
    `aes128_key_schedule(key)` then `decrypt_block`.

### Comments

17. Added `// ADAPTATION:` comments above the new type definitions and the
    entry points, and doc comments on the added items.  Upstream comments
    and doc comments of kept items are unchanged; those of removed items are
    gone with them.
