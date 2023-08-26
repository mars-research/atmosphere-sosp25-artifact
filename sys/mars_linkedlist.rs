use super::*;
    
verus! {

pub struct Needle{

}

pub struct MarsLinkedList{
    pub spec_seq: Ghost<Seq<usize>>,
    pub len: usize,
    pub capacity: usize,
}

impl MarsLinkedList {
    
    pub open spec fn wf(&self) -> bool{
        true
    }

    pub open spec fn spec_capacity(&self) -> usize{
        self.capacity
    }

    #[verifier(external_body)]
    #[verifier(when_used_as_spec(spec_capacity))]
    pub fn capacity(&self) -> (l: usize)
        ensures
            l == self.capacity,
    {
        self.capacity
    }

    pub open spec fn spec_len(&self) -> usize{
        self.len
    }

    #[verifier(external_body)]
    #[verifier(when_used_as_spec(spec_len))]
    pub fn len(&self) -> (l: usize)
        ensures
            l == self.len,
    {
        self.len
    }

    pub open spec fn view(&self) -> Seq<usize>
        recommends self.wf(),
    {
        self.spec_seq@
    }

    ///Spec for Needle is not decided yet.
    pub open spec fn needle_valid(&self, needle: &Needle) -> bool
        recommends self.wf(),
    {
        true
    }

    pub open spec fn needle_resolve(&self, needle: &Needle) -> usize
        recommends self.wf(),   
                   self.needle_valid(needle),
    {
        0
    }

    pub open spec fn is_unique(&self) -> bool {
        forall|i:int, j:int| #![auto] i != j && 0 <= i < self.len() && 0 <= j < self.len()
            ==> self@[i] != self@[j]
    }

    #[verifier(external_body)]
    pub fn get_head_needle(&self) -> (ret: Needle)
        requires self.wf(),   
                 self.len() > 0,
        ensures  self.needle_valid(&ret),
                 self.needle_resolve(&ret) == self@[0],
    {
        return Needle{};
    }

    #[verifier(external_body)]
    pub fn push(&mut self, new_value: usize) -> (ret: Needle)
        requires 
            old(self).wf(),
            old(self).len() < old(self).capacity(),
        ensures 
            self.wf(),
            self@ == old(self)@.push(new_value),
            self.len() == old(self).len() + 1,
            self.needle_valid(&ret),
            self.needle_resolve(&ret) == new_value,
            forall| ptr: usize| ptr != new_value ==> old(self)@.contains(ptr) == self@.contains(ptr),
            self@.contains(new_value),
            forall| needle: Needle| old(self).needle_valid(&needle) ==> self.needle_valid(&needle),
            forall| needle: Needle| old(self).needle_valid(&needle) ==> self.needle_resolve(&needle) == old(self).needle_resolve(&needle),
    {
        return Needle{};
    }

    #[verifier(external_body)]
    pub fn pop(&mut self) -> (ret: (usize,Needle))
        requires 
            old(self).wf(),
            old(self).len() > 0,
        ensures 
            self.wf(),
            self@ == old(self)@.subrange(1,old(self).len() as int),
            self.len() == old(self).len() - 1,
            forall| ptr: usize| ptr != ret.0 ==> old(self)@.contains(ptr) == self@.contains(ptr),
            self@.contains(ret.0) == false,
            ret.0 == old(self)@[0],
            old(self).needle_valid(&ret.1),
            old(self).needle_resolve(&ret.1) == old(self)@[0],
            forall| needle: Needle| old(self).needle_valid(&needle) && needle != ret.1 ==> self.needle_valid(&needle),
            forall| needle: Needle| old(self).needle_valid(&needle) && needle != ret.1 ==> self.needle_resolve(&needle) == old(self).needle_resolve(&needle),
    {
        (0,Needle{})
    }

    #[verifier(external_body)]
    pub fn remove(&mut self, needle: &Needle) -> (ret: usize)
        requires old(self).wf(),
                 old(self).needle_valid(needle),
                 old(self)@.contains(old(self).needle_resolve(needle)),
                 old(self).is_unique(),
        ensures self.wf(),
                self.len() == old(self).len() - 1,
                ret == old(self).needle_resolve(needle),
                self@ == old(self)@.subrange(0,old(self)@.index_of(old(self).needle_resolve(needle))).
                    add(old(self)@.subrange(old(self)@.index_of(old(self).needle_resolve(needle)) + 1, old(self)@.len() as int)), 
                forall| value:usize|  #![auto]  ret != value ==> old(self)@.contains(value) == self@.contains(value),
                self@.contains(ret) == false,
                self.is_unique(),
                forall| _needle: Needle| old(self).needle_valid(&_needle) && _needle != needle ==> self.needle_valid(&_needle),
                forall| _needle: Needle| old(self).needle_valid(&_needle) && _needle != needle ==> self.needle_resolve(&_needle) == old(self).needle_resolve(&_needle),
    {
        0
    }
}
}