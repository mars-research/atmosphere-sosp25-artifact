use vstd::prelude::*;
use core::mem::MaybeUninit;
verus!{
    #[repr(align(4096))]
    pub struct DeviceTable{
        ar:[usize;512],
    }


    // impl DeviceTable{
    //     pub open spec fn wf(&self) {
    //         self.seq_ar@.len() == 256,
    //     }
            
    //     #[verifier(inline)]
    //     pub fn get(&self, dev:usize, fun:usize) -> (ret:usize)
    //         requires    
    //             self.wf(),
    //             0<=dev<32,
    //             0<=fun<8,
    //         ensures
    //             ret == self.seq_ar@[dev*fun]
    //     {
    //         return self.ar[dev*fun];
    //     }

    //     #[verifier(inline)]
    //     pub fn set(&mut self, dev:usize, fun:usize, cr3:usize) -> (ret:usize)
    //         requires    
    //             self.wf(),
    //             0<=dev<32,
    //             0<=fun<8,
    //         ensures
    //             ret == self.seq_ar@.update(dev*fun, cr3);
    //             self.wf(),
    //     {
    //         self.ar[dev*fun] = cr3;
    //     }
    // }

    #[repr(align(4096))]
    pub struct RootTable{
        root:[usize;512],
        seq_ar: Ghost<Seq<Seq<Seq<usize>>>>,

        deviecs:[DeviceTable;256],
    }

    impl RootTable{

        #[verifier(external_body)]
        pub fn new() -> (ret: Self)
        {
            unsafe{
                RootTable{
                    root: MaybeUninit::uninit().assume_init(),
                    seq_ar: Ghost(Seq::empty()),
                    
                    deviecs: MaybeUninit::uninit().assume_init(),
                }
            }
        }

        #[verifier(external_body)]
        pub fn init(&mut self)
            ensures
                self.wf(),
                forall|bus:usize,dev:usize,fun:usize|#![auto] 0<=bus<256 && 0<=dev<32 && 0<=fun<8 ==> self.resolve(bus,dev,fun) == 0,
        {
            let mut i = 0;
            while i != 256 {
                self.root[i] = &self.deviecs[i] as * const DeviceTable as usize;
                i = i + 1;
            }
            let mut i = 0;
            let mut j = 0;
            while i != 256 {
                j = 0;
                while j != 256{
                    self.deviecs[i].ar[j] = 0;
                    j = j + 1;
                }
                i = i + 1;
            }
        }

        pub closed spec fn wf(&self) -> bool{
            self.seq_ar@.len() == 256
            &&
            forall|bus:usize|#![auto] 0<=bus<256 ==> self.seq_ar@[bus as int].len() == 32
            &&
            forall|bus:usize,dev:usize|#![auto] 0<=bus<256 && 0<=dev<32 ==> self.seq_ar@[bus as int][dev as int].len() == 8
        }

        pub closed spec fn resolve(&self, bus:usize, dev:usize, fun:usize) -> usize
            recommends
                self.wf(),
                0<=bus<256 && 0<=dev<32 && 0<=fun<8,
        {
            self.seq_ar@[bus as int][dev as int][fun as int]
        }

        #[verifier(external_body)]
        pub fn get(&self, bus:usize, dev:usize, fun:usize) -> (ret: usize)
            requires
                self.wf(),
                0<=bus<256 && 0<=dev<32 && 0<=fun<8,
            ensures
                ret == self.resolve(bus,dev,fun)
        {
            self.deviecs[bus].ar[dev*fun]
        }
 
        #[verifier(external_body)]
        pub fn set(&mut self, bus:usize, dev:usize, fun:usize, target:usize)
            requires
                old(self).wf(),
                0<=bus<256 && 0<=dev<32 && 0<=fun<8,
            ensures
                self.wf(),
                self.resolve(bus,dev,fun) == target,
                forall|_bus:usize,_dev:usize,_fun:usize|#![auto] 0<=_bus<256 && 0<=_dev<32 && 0<=_fun<8 && 
                    (_bus != bus || _dev != dev || _fun != fun) 
                    ==> self.resolve(_bus,_dev,_fun) == old(self).resolve(_bus,_dev,_fun)
        {
            self.deviecs[bus].ar[dev*fun] = target;
        }       
    }
}