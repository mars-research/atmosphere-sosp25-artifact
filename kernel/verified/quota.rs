use vstd::prelude::*;
verus! {
    use crate::define::*;

    #[derive(Clone, Copy, Debug)]
    pub struct Quota{
        pub mem_4k:usize,
        pub mem_2m:usize,
        pub mem_1g:usize,
        pub pcid:usize,
        pub ioid:usize,
    }

    impl Quota{
        pub open spec fn spec_set_mem_4k(&self, v:usize) -> Self
        {
            Self{
                mem_4k:v,
                mem_2m:self.mem_2m,
                mem_1g:self.mem_1g,
                pcid:self.pcid,
                ioid:self.ioid,
            }
        }
        pub fn set_mem_4k(&mut self, v:usize) 
            ensures
                old(self).spec_set_mem_4k(v) == self,
        {
            self.mem_4k = v;
        }

        pub open spec fn spec_subtract_mem_4k(&self, new:Self, k:usize) -> bool
        {
           &&&
           self.mem_4k - k == new.mem_4k
           &&&
           self.mem_2m == new.mem_2m
           &&&
           self.mem_1g == new.mem_1g
           &&&
           self.pcid == new.pcid
           &&&
           self.ioid == new.ioid
        }
        pub fn subtract_mem_4k(&mut self, v:usize) 
            requires
                old(self).mem_4k >= v,
            ensures
                old(self).spec_subtract_mem_4k(*self, v),
        {
            self.mem_4k = self.mem_4k - v;
        }

        pub open spec fn spec_set_mem_2m(&self, v:usize) -> Self
        {
            Self{
                mem_4k:self.mem_4k,
                mem_2m:v,
                mem_1g:self.mem_1g,
                pcid:self.pcid,
                ioid:self.ioid,
            }
        }
        pub fn set_mem_2m(&mut self, v:usize) 
            ensures
                old(self).spec_set_mem_2m(v) == self,
        {
            self.mem_2m = v;
        }
        pub open spec fn spec_set_mem_1g(&self, v:usize) -> Self
        {
            Self{
                mem_4k:self.mem_4k,
                mem_2m:self.mem_2m,
                mem_1g:v,
                pcid:self.pcid,
                ioid:self.ioid,
            }
        }
        pub fn set_mem_1g(&mut self, v:usize) 
            ensures
                old(self).spec_set_mem_1g(v) == self,
        {
            self.mem_1g = v;
        }
        pub open spec fn spec_set_pcid(&self, v:usize) -> Self
        {
            Self{
                mem_4k:self.mem_4k,
                mem_2m:self.mem_2m,
                mem_1g:self.mem_1g,
                pcid:v,
                ioid:self.ioid,
            }
        }
        pub fn set_pcid(&mut self, v:usize) 
            ensures
                old(self).spec_set_pcid(v) == self,
        {
            self.pcid = v;
        }
        pub open spec fn spec_set_ioid(&self, v:usize) -> Self
        {
            Self{
                mem_4k:self.mem_4k,
                mem_2m:self.mem_2m,
                mem_1g:self.mem_1g,
                pcid:self.pcid,
                ioid: v,
            }
        }
        pub fn set_ioid(&mut self, v:usize) 
            ensures
                old(self).spec_set_ioid(v) == self,
        {
            self.ioid = v;
        }

        pub open spec fn spec_greater(&self, new:&Quota) -> bool
        {
            &&&
            self.mem_4k >= new.mem_4k
            &&&
            self.mem_2m >= new.mem_2m
            &&&
            self.mem_1g >= new.mem_1g
            &&&
            self.pcid >= new.pcid
            &&&
            self.ioid >= new.ioid
        }

        pub open spec fn spec_subtract_new_quota(&self, self_new:&Self, new:&Quota) -> bool
        {
            &&&
            self.mem_4k - new.mem_4k == self_new.mem_4k
            &&&
            self.mem_2m - new.mem_2m == self_new.mem_2m
            &&&
            self.mem_1g - new.mem_1g == self_new.mem_1g
            &&&
            self.pcid - new.pcid == self_new.pcid
            &&&
            self.ioid - new.ioid == self_new.ioid
        }
        pub fn subtract_new_quota(&mut self, new:&Quota)
            requires
                old(self).mem_4k >= new.mem_4k,
                old(self).mem_2m >= new.mem_2m,
                old(self).mem_1g >= new.mem_1g,
                old(self).pcid >= new.pcid,
                old(self).ioid >= new.ioid,
            ensures
                old(self).spec_subtract_new_quota(self, new),
        {
            self.mem_4k = self.mem_4k - new.mem_4k;
            self.mem_2m = self.mem_2m - new.mem_2m;
            self.mem_1g = self.mem_1g - new.mem_1g;
            self.pcid = self.pcid - new.pcid;
            self.ioid = self.ioid - new.ioid;
        }
    }
}