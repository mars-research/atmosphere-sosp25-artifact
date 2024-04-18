use core::mem::MaybeUninit;
use core::mem;

pub const CAPACITY: usize = ((1usize << 20) * 2);

/* maglev KV pair */
#[derive(Copy,Clone)]
pub struct maglev_kv_pair {
    key:usize,
    value:usize,
}

impl maglev_kv_pair{
    pub const fn new() -> Self{
        Self{
            key:0,
            value:0,
        }
    }
}

pub const ETH_HEADER_LEN: usize = 14;
pub const UDP_HEADER_LEN: usize = 8;

// https://en.wikipedia.org/wiki/IPv4
pub const IPV4_PROTO_OFFSET: usize = 9;
pub const IPV4_LENGTH_OFFSET: usize = 2;
pub const IPV4_CHECKSUM_OFFSET: usize = 10;
pub const IPV4_SRCDST_OFFSET: usize = 12;
pub const IPV4_SRCDST_LEN: usize = 8;
pub const UDP_LENGTH_OFFSET: usize = 4;
pub const UDP_CHECKSUM_OFFSET: usize = 6;

pub const TABLE_SIZE: usize = 65537;

#[repr(C)]
#[derive(Debug)]
struct rte_ether_addr{
    pub addr_bytes: [u8;6], 
}

#[repr(C)]
#[derive(Debug)]
pub struct rte_ether_hdr {
    pub dst_addr: rte_ether_addr,
    pub src_addr: rte_ether_addr, 
    pub ether_type: u16,
}

pub type Node = u32;
pub type LookUpTable = [i8;TABLE_SIZE];

pub struct MaglevHashmap{
    pairs:[maglev_kv_pair;CAPACITY],
}
impl MaglevHashmap{
    pub const fn new() -> Self{
        Self{
            pairs:[maglev_kv_pair::new();CAPACITY],
        } 
        

    }
}

pub const FNV_BASIS: usize = 0xcbf29ce484222325usize;
pub const FNV_PRIME: usize = 0x100000001b3;

pub static mut maglev_lookup:LookUpTable = [0;TABLE_SIZE];
pub static mut map:MaglevHashmap = MaglevHashmap::new();

#[inline(always)]
pub fn fnv_1_multi(data:*mut u8, len:usize, mut state:usize) -> usize {
	for i in 0..len {
		state *= FNV_PRIME;
        
        unsafe{
            // log::info!("data @ {:x?} data[{}] {:x}", data, i, *(((data as usize) + i) as *mut u8));
            state ^= *(((data as usize) + i) as *mut u8) as usize;
        }
	}
	return state;
}

#[inline(always)]
pub fn fnv_1(data:*mut u8, len:usize) -> usize {
	return fnv_1_multi(data, len, FNV_BASIS);
}

#[inline(always)]
pub fn fnv_1a(data:*mut u8, len:usize) -> usize {
	return fnv_1_multi(data, len, FNV_BASIS);
}

#[inline(always)]
pub fn fnv_1a_multi(data:*mut u8, len:usize, mut state:usize) -> usize {
	for i in 0..len {
		unsafe{state ^= *(((data as usize) + i) as *mut u8) as usize;}
		state *= FNV_PRIME;
	}
	return state;
}

#[inline(always)]
pub fn fnv_1_multi_usize(data:usize, mut state:usize) -> usize {
	for i in 0..8 {
		state *= FNV_PRIME;
		state ^= (data & (0xFF<<i))>>i;
	}
	return state;
}

#[inline(always)]
pub fn fnv_1_usize(data:usize) -> usize {
	return fnv_1_multi_usize(data, FNV_BASIS);
}
#[inline(always)]
pub fn fnv_1a_usize(data:usize) -> usize {
	return fnv_1_multi_usize(data, FNV_BASIS);
}

#[inline(always)]
pub fn fnv_1a_multi_usize(data:usize, mut state:usize) -> usize {
	for i in 0..8 {
	    state ^= (data & (0xFF<<i))>>i;
		state *= FNV_PRIME;
	}
	return state;
}

#[inline(always)]
pub fn fnv_1_multi_u32(data:u32, mut state:usize) -> usize {
	for i in 0..4 {
		state *= FNV_PRIME;
		state ^= ((data & (0xFF<<i))>>i) as usize;
	}
	return state;
}

#[inline(always)]
pub fn fnv_1_u32(data:u32) -> usize {
	return fnv_1_multi_u32(data, FNV_BASIS);
}

#[inline(always)]
pub fn fnv_1a_u32(data:u32) -> usize {
	return fnv_1_multi_u32(data, FNV_BASIS);
}

#[inline(always)]
pub fn fnv_1a_multi_u32(data:u32, mut state:usize) -> usize {
	for i in 0..4 {
	    state ^= ((data & (0xFF<<i))>>i) as usize;
		state *= FNV_PRIME;
	}
	return state;
}

#[inline(always)]
pub fn flowhash(frame:*mut u8, len:usize) -> usize {
	// Warning: This implementation returns 0 for invalid inputs
	
    unsafe{
        let f = frame;

        // Fail early
        if (*(((f as usize) + ETH_HEADER_LEN) as *mut u8) as usize >> 4 != 4) {
            // This shitty implementation can only handle IPv4 :(
            log::info!("\n");
            // return 0;
        }
    
        let proto = *(((f as usize) + ETH_HEADER_LEN + IPV4_PROTO_OFFSET) as *mut u8) as usize;
        if (proto != 6 && proto != 17) {
            // This shitty implementation can only handle TCP and UDP
            log::info!("Unhandled proto {:x}\n", proto);
            return 0;
        }
    
        let v4len:usize = 4 * (*(((f as usize) + ETH_HEADER_LEN) as *mut u8) as usize & 0b1111) as usize;
        if (len < (ETH_HEADER_LEN + v4len + 4)) {
            // Not long enough
            log::info!("header len short len {} expected {} \n", len, (ETH_HEADER_LEN + v4len + 4));
            //hexdump(f, 64);
            return 0;
        }
    
        let mut hash:usize = FNV_BASIS;
    
        // Hash source/destination IP addresses
        hash = fnv_1_multi((((f as usize) + ETH_HEADER_LEN + IPV4_SRCDST_OFFSET) as *mut u8), IPV4_SRCDST_LEN, hash);
    
        // Hash IP protocol number
        hash = fnv_1_multi((((f as usize) + ETH_HEADER_LEN + IPV4_PROTO_OFFSET) as *mut u8), 1, hash);
    
        // Hash source/destination port
        hash = fnv_1_multi((((f as usize) + ETH_HEADER_LEN + v4len) as *mut u8), 4, hash);

        hash = fnv_1_multi((((f as usize) + 24 ) as *mut u8), 2, hash);
    
        return hash;
    }
}

#[inline(always)]
fn get_offset_skip(node:*mut Node, offset: *mut usize, skip: *mut usize) {
    unsafe{
        *offset = fnv_1(node as *mut u8, mem::size_of::<Node>()) % (TABLE_SIZE - 1) + 1;
        *skip = fnv_1a(node as *mut u8, mem::size_of::<Node>()) % TABLE_SIZE;
    }
}

#[inline(always)]
fn get_permutation(node:Node, j:usize) -> usize {
    let mut offset = 0;
    let mut skip = 0;
    offset = fnv_1_u32(node) % (TABLE_SIZE - 1) + 1;
    skip = fnv_1a_u32(node) % TABLE_SIZE;
    return (offset + j * skip) % TABLE_SIZE;
}

#[inline(always)]
fn populate_lut(lut: &mut LookUpTable) {
    log::info!("hello from populate_lut");
    // The nodes are meaningless, just like my life
    let mut nodes:[Node;3] = [800, 273, 8255];
    let mut next:[usize;3] = [0, 0, 0];

    for i in 0..TABLE_SIZE {
        lut[i] = -1;
    }

    let mut n = 0usize;

    loop {
        for i in 0..3 {
            // let c = 0;
            let mut c = get_permutation(nodes[i], next[i]);
            while (lut[c] >= 0) {
                next[i] += 1;
                c = get_permutation(nodes[i], next[i]);
            }

            lut[c] = i as i8;
            next[i] += 1;
            n += 1;

            if (n == TABLE_SIZE) {
                return;
            }
        }
    }
}

#[inline(always)]
fn maglev_hashmap_insert(key:usize, value:usize)
{
    unsafe{
        let hash = fnv_1_usize(key);
        for i in 0..CAPACITY{
            let probe = hash + i;
            let mut pair = &mut map.pairs[probe % CAPACITY];
            if (pair.key == key || pair.key == 0) {
                pair.key = key;
                pair.value = value;
                break;
            }
        }
    }
    //uint64_t hash = hash_fn(key);
}

#[inline(always)]
fn maglev_hashmap_get(key:usize) -> Option<*mut maglev_kv_pair>
{
    unsafe{
    //uint64_t hash = hash_fn(key);
    let hash = fnv_1_usize(key);
    for i in 0..CAPACITY {
        let probe = hash + i;
        let mut pair = &mut map.pairs[probe % CAPACITY];
        if (pair.key == 0) {
            return None;
        }
        if (pair.key == key) { // hacky, uses zero key as empty marker
            return Some(pair as *mut maglev_kv_pair);
        }
    }

    return None;
    }
}

#[inline(always)]
pub fn maglev_process_frame(frame: *mut rte_ether_hdr, len: usize) -> usize {
    unsafe{
        let mut backend:usize = 0xFFFFFFFF;
        let hash = flowhash(frame as *mut u8, len);
        // log::info!("hash: {:x}", hash);
        if (hash != 0) {
            let cached = maglev_hashmap_get(hash);
            if (cached.is_none()) {
                // Use lookup table
                backend = maglev_lookup[hash % TABLE_SIZE] as usize;
                maglev_hashmap_insert(hash, backend);
            } else {
                backend = (*(cached.unwrap())).value;
                // Just use the cached backend (noop in this test)
            }
    
        }
        return backend;
    }
}

#[inline(always)]
pub fn maglev_init() {
    
    log::info!("hello from maglev_init");
    unsafe{
        populate_lut(&mut maglev_lookup);
    }
}