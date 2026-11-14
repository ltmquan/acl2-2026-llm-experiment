# Produce /work/subject/src/lib.rs from the pristine upstream fixslice32.rs.
import re,sys
src=open(sys.argv[1]).read().split('\n')
L=lambda a,b: src[a-1:b]   # 1-based inclusive
def find(pat,start=0):
    for i in range(start,len(src)):
        if re.match(pat,src[i]): return i+1
    raise Exception(pat)
out=[]
out+=L(1,16)
out+=["",
"// ADAPTATION: byte arrays replace the `cipher` crate's `Array` types",
"// (upstream: `use crate::Block;` with `Block = Array<u8, U16>`, and",
"// `BatchBlocks = Array<Block, FixsliceBlocks>` with `FixsliceBlocks = U2`).",
"/// AES block",
"pub type Block = [u8; 16];",
"",
"/// AES block batch: two blocks",
"pub(crate) type BatchBlocks = [Block; 2];",
""]
# AES-128 round keys and State, verbatim
k=find(r'/// AES-128 round keys')
out+=L(k,k+1)+[""]
st=find(r'/// 256-bit internal state')
out+=L(st,st+1)+[""]
ks=find(r'/// Fully bitsliced AES-128 key schedule')
ks_end=find(r'^}',ks)
out+=L(ks,ks_end)
# aes128_decrypt and aes128_encrypt
d=find(r'/// Fully-fixsliced AES-128 decryption')
e_end=find(r'^}',find(r'pub\(crate\) fn aes128_encrypt'))
out+=[""]+L(d,e_end)
# rest: from inv_sub_bytes doc to before hazmat
r=find(r'/// Note that the 4 bitwise NOT .* are accounted for here')
h=find(r'/// Low-level "hazmat" AES functions')
out+=[""]+L(r,h-1)
text='\n'.join(out)
# drop the untaken compact cfg paths and the cfg gates on the taken ones
def strip_cfg(text):
    lines=text.split('\n'); res=[]; i=0
    while i<len(lines):
        s=lines[i].strip()
        if s=='#[cfg(aes_backend_soft = "compact")]' and lines[i+1].strip()=='{':
            ind=len(lines[i+1])-len(lines[i+1].lstrip())
            j=i+2
            while not (lines[j].strip()=='}' and len(lines[j])-len(lines[j].lstrip())==ind): j+=1
            i=j+1
            # remove a following blank line if the previous kept line is blank
            if res and (res[-1].strip()=='' or res[-1].rstrip().endswith('{')) and i<len(lines) and lines[i].strip()=='': i+=1
            continue
        if s=='#[cfg(not(aes_backend_soft = "compact"))]':
            nxt=lines[i+1]
            if nxt.strip()=='{':
                ind=len(nxt)-len(nxt.lstrip())
                j=i+2
                while not (lines[j].strip()=='}' and len(lines[j])-len(lines[j].lstrip())==ind): j+=1
                for k in range(i+2,j):
                    res.append(lines[k][4:] if lines[k].startswith(' '*(ind+4)) else lines[k])
                i=j+1; continue
            i+=1; continue
        if s=='#[cfg(any(not(aes_backend_soft = "compact"), feature = "hazmat"))]':
            i+=1; continue
        res.append(lines[i]); i+=1
    return '\n'.join(res)
text=strip_cfg(text)
old="    let mut output = BatchBlocks::default();"
assert old in text
text=text.replace(old,"    let mut output: BatchBlocks = [[0u8; 16]; 2];")
text=text.rstrip()+'\n'
text+='''
// ---------------------------------------------------------------------------
// ADAPTATION: single-block entry points (replacing the `cipher` crate trait
// implementations of `soft.rs`).  Each duplicates the block into both lanes of
// a batch, runs the two-lane function, and returns lane 0.

/// Encrypt one block with precomputed round keys.
pub fn encrypt_block(rkeys: &FixsliceKeys128, block: &Block) -> Block {
    let blocks: BatchBlocks = [*block, *block];
    let res = aes128_encrypt(rkeys, &blocks);
    res[0]
}

/// Decrypt one block with precomputed round keys.
pub fn decrypt_block(rkeys: &FixsliceKeys128, block: &Block) -> Block {
    let blocks: BatchBlocks = [*block, *block];
    let res = aes128_decrypt(rkeys, &blocks);
    res[0]
}

/// AES-128 encryption of one block: key schedule, then `encrypt_block`.
pub fn encrypt(key: &[u8; 16], block: &Block) -> Block {
    let rkeys = aes128_key_schedule(key);
    encrypt_block(&rkeys, block)
}

/// AES-128 decryption of one block: key schedule, then `decrypt_block`.
pub fn decrypt(key: &[u8; 16], block: &Block) -> Block {
    let rkeys = aes128_key_schedule(key);
    decrypt_block(&rkeys, block)
}
'''
open(sys.argv[2],'w').write(text)
