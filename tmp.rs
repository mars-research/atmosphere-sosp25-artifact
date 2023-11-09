assert(self.endpoint_ptrs@.finite());
assert(self.endpoint_ptrs@ =~= self.endpoint_perms@.dom());
assert(self.endpoint_perms@.dom().contains(0) == false);
assert(forall|endpoint_ptr: EndpointPtr| #![auto] self.endpoint_perms@.dom().contains(endpoint_ptr) ==>  self.endpoint_perms@[endpoint_ptr].view().value.is_Some());
assert(forall|endpoint_ptr: EndpointPtr| #![auto] self.endpoint_perms@.dom().contains(endpoint_ptr) ==>  self.endpoint_perms@[endpoint_ptr].view().pptr == endpoint_ptr);
assert(forall|endpoint_ptr: EndpointPtr| #![auto] self.endpoint_perms@.dom().contains(endpoint_ptr) ==>  self.endpoint_perms@[endpoint_ptr].view().value.get_Some_0().queue.wf());
assert(forall|endpoint_ptr: EndpointPtr| #![auto] self.endpoint_perms@.dom().contains(endpoint_ptr) ==>  self.endpoint_perms@[endpoint_ptr].view().value.get_Some_0().queue.unique());
assert(forall|endpoint_ptr: EndpointPtr| #![auto] self.endpoint_perms@.dom().contains(endpoint_ptr) ==>  self.endpoint_perms@[endpoint_ptr].view().value.get_Some_0().owning_threads@.finite());
assert(forall|endpoint_ptr: EndpointPtr| #![auto] self.endpoint_perms@.dom().contains(endpoint_ptr) 
    ==> self.endpoint_perms@[endpoint_ptr]@.value.get_Some_0().owning_threads@.len() == self.endpoint_perms@[endpoint_ptr]@.value.get_Some_0().rf_counter);

assert(forall|endpoint_ptr: EndpointPtr| #![auto] self.endpoint_perms@.dom().contains(endpoint_ptr) 
    ==> self.endpoint_perms@[endpoint_ptr]@.value.get_Some_0().rf_counter != 0);
assert(forall|endpoint_ptr: EndpointPtr| #![auto] self.endpoint_perms@.dom().contains(endpoint_ptr) 
    ==> (forall|thread_ptr: ThreadPtr| #![auto] self.endpoint_perms@[endpoint_ptr]@.value.get_Some_0().owning_threads@.contains(thread_ptr)
        ==> self.thread_perms@.dom().contains(thread_ptr))
);

assert(forall|endpoint_ptr: EndpointPtr| #![auto] self.endpoint_perms@.dom().contains(endpoint_ptr) 
    ==> (forall|thread_ptr: ThreadPtr| #![auto] self.endpoint_perms@[endpoint_ptr]@.value.get_Some_0().owning_threads@.contains(thread_ptr)
        ==> self.thread_perms@[thread_ptr]@.value.get_Some_0().endpoint_descriptors@.contains(endpoint_ptr))
);

assert(forall|endpoint_ptr: EndpointPtr| #![auto] self.endpoint_perms@.dom().contains(endpoint_ptr) 
    ==>  (forall|thread_ptr:ThreadPtr| #![auto] self.endpoint_perms@[endpoint_ptr]@.value.get_Some_0().queue@.contains(thread_ptr)
        ==> ( self.thread_perms@.dom().contains(thread_ptr)
        )
));

assert(forall|endpoint_ptr: EndpointPtr| #![auto] self.endpoint_perms@.dom().contains(endpoint_ptr) 
    ==>  (forall|thread_ptr:ThreadPtr| #![auto] self.endpoint_perms@[endpoint_ptr]@.value.get_Some_0().queue@.contains(thread_ptr)
        ==> (
            self.thread_perms@[thread_ptr]@.value.get_Some_0().state == BLOCKED
        )
));

assert(forall|endpoint_ptr: EndpointPtr| #![auto] self.endpoint_perms@.dom().contains(endpoint_ptr) 
    ==>  (forall|thread_ptr:ThreadPtr| #![auto] self.endpoint_perms@[endpoint_ptr]@.value.get_Some_0().queue@.contains(thread_ptr)
        ==> (
            self.thread_perms@[thread_ptr]@.value.get_Some_0().endpoint_ptr.unwrap() == endpoint_ptr
        )
));

assert(forall|thread_ptr: ThreadPtr| #![auto] self.thread_perms@.dom().contains(thread_ptr) 
    ==> self.thread_perms@[thread_ptr]@.value.get_Some_0().endpoint_descriptors.wf());

assert(forall|thread_ptr: ThreadPtr| #![auto] self.thread_perms@.dom().contains(thread_ptr) 
    ==> endpoint_descriptors_unique(self.thread_perms@[thread_ptr]@.value.get_Some_0().endpoint_descriptors)
    );

assert(forall|thread_ptr: ThreadPtr| #![auto] self.thread_perms@.dom().contains(thread_ptr) 
    ==> (forall|i:int| #![auto] 0<=i<MAX_NUM_ENDPOINT_DESCRIPTORS && self.thread_perms@[thread_ptr].view().value.get_Some_0().endpoint_descriptors@[i] != 0
        ==> self.endpoint_perms@.dom().contains(self.thread_perms@[thread_ptr].view().value.get_Some_0().endpoint_descriptors@[i])
    ));

assert(forall|thread_ptr: ThreadPtr| #![auto] self.thread_perms@.dom().contains(thread_ptr) 
    ==> (forall|i:int| #![auto] 0<=i<MAX_NUM_ENDPOINT_DESCRIPTORS && self.thread_perms@[thread_ptr].view().value.get_Some_0().endpoint_descriptors@[i] != 0
        ==> self.endpoint_perms@[self.thread_perms@[thread_ptr].view().value.get_Some_0().endpoint_descriptors@[i]]@.value.get_Some_0().owning_threads@.contains(thread_ptr)
    ));

assert(forall|thread_ptr: ThreadPtr| #![auto] self.thread_perms@.dom().contains(thread_ptr) && self.thread_perms@[thread_ptr].view().value.get_Some_0().state == BLOCKED
    ==> self.thread_perms@[thread_ptr]@.value.get_Some_0().endpoint_ptr.is_Some());

assert(forall|thread_ptr: ThreadPtr| #![auto] self.thread_perms@.dom().contains(thread_ptr) && self.thread_perms@[thread_ptr].view().value.get_Some_0().state == BLOCKED
    ==> self.thread_perms@[thread_ptr]@.value.get_Some_0().endpoint_ptr.unwrap() != 0);

assert(forall|thread_ptr: ThreadPtr| #![auto] self.thread_perms@.dom().contains(thread_ptr) && self.thread_perms@[thread_ptr].view().value.get_Some_0().state == BLOCKED
    ==>  self.thread_perms@[thread_ptr]@.value.get_Some_0().endpoint_descriptors@.contains(self.thread_perms@[thread_ptr].view().value.get_Some_0().endpoint_ptr.unwrap()));

assert(forall|thread_ptr: ThreadPtr| #![auto] self.thread_perms@.dom().contains(thread_ptr) && self.thread_perms@[thread_ptr].view().value.get_Some_0().state == BLOCKED
    ==> self.thread_perms@[thread_ptr]@.value.get_Some_0().endpoint_rf.is_Some());

assert(forall|thread_ptr: ThreadPtr| #![auto] self.thread_perms@.dom().contains(thread_ptr) && self.thread_perms@[thread_ptr].view().value.get_Some_0().state == BLOCKED
    ==>  self.endpoint_perms@[self.thread_perms@[thread_ptr].view().value.get_Some_0().endpoint_ptr.unwrap()]@.value.get_Some_0().queue@.contains(thread_ptr));

assert(forall|thread_ptr: ThreadPtr| #![auto] self.thread_perms@.dom().contains(thread_ptr) && self.thread_perms@[thread_ptr].view().value.get_Some_0().state == BLOCKED
    ==>  self.endpoint_perms@[self.thread_perms@[thread_ptr].view().value.get_Some_0().endpoint_ptr.unwrap()]@.value.get_Some_0().queue.node_ref_valid(self.thread_perms@[thread_ptr].view().value.get_Some_0().endpoint_rf.unwrap())
);

assert(forall|thread_ptr: ThreadPtr| #![auto] self.thread_perms@.dom().contains(thread_ptr) && self.thread_perms@[thread_ptr].view().value.get_Some_0().state == BLOCKED
    ==>  self.endpoint_perms@[self.thread_perms@[thread_ptr].view().value.get_Some_0().endpoint_ptr.unwrap()]@.value.get_Some_0().queue.node_ref_resolve(self.thread_perms@[thread_ptr].view().value.get_Some_0().endpoint_rf.unwrap()) == thread_ptr
);