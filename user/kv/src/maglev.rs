use core::mem::MaybeUninit;
use core::mem;
use core::ptr;

pub const CAPACITY: usize = (1usize << 20) * 8;
pub const K_SIZE: usize = 32;
pub const V_SIZE: usize = 32;

/* maglev KV pair */
#[derive(Copy,Clone)]
pub struct maglev_kv_pair {
    key:[u8;K_SIZE],
    value:[u8;V_SIZE],
}

impl maglev_kv_pair{
    pub const fn new() -> Self{
        Self{
            key:[0;K_SIZE],
            value:[0;V_SIZE],
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


pub type Node = u32;

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
pub fn maglev_hashmap_insert(key:*mut u8, value:*mut u8)
{
    unsafe{
        let hash = fnv_1(key,K_SIZE);
        for i in 0..CAPACITY{
            let probe = hash + i;
            let mut pair = &mut map.pairs[probe % CAPACITY];
            let k = unsafe { core::slice::from_raw_parts(key, K_SIZE) };
            // log::info!("key: {:?}",k);
            // log::info!("value: {:?}",unsafe { core::slice::from_raw_parts(value, V_SIZE) });
            // log::info!("pair.key: {:?}",pair.key);
            // log::info!("pair.value: {:?}",pair.value);
            let empty_k = unsafe { core::slice::from_raw_parts(&[0u8;K_SIZE] as *const u8, K_SIZE) };

            if (k == pair.key || pair.key == empty_k) {
                ptr::copy(
                    key as *mut u8,
                    pair.key.as_mut_ptr(),
                    K_SIZE,
                );
                ptr::copy(
                    value as *mut u8,
                    pair.value.as_mut_ptr(),
                    V_SIZE,
                );
                break;
            }
        }
    }
    //uint64_t hash = hash_fn(key);
}

#[inline(always)]
pub fn maglev_hashmap_get(key:*mut u8) -> Option<*mut maglev_kv_pair>
{
    unsafe{
    //uint64_t hash = hash_fn(key);
    let hash = fnv_1(key, K_SIZE);
    for i in 0..CAPACITY {
        let probe = hash + i;
        let mut pair = &mut map.pairs[probe % CAPACITY];
        if (pair.key == unsafe { core::slice::from_raw_parts(&[0u8;K_SIZE] as *const u8, K_SIZE) } ) {
            return None;
        }
        if (pair.key == unsafe { core::slice::from_raw_parts(key, K_SIZE) } ) { // hacky, uses zero key as empty marker
            ptr::copy(
                pair.value.as_ptr(),
                ((key) as *mut u8),
                V_SIZE,
            );
            return Some(pair as *mut maglev_kv_pair);
        }
    }

    return None;
    }
}

