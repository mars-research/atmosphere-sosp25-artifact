use core::slice;
use alloc::rc::Rc;
use core::cell::RefCell;

use ring_buffer::{IxgbeRingBuffer, IxgbePayLoad};
use ixgbe_driver::device::IxgbeDevice;

use smoltcp::phy::{Checksum, ChecksumCapabilities, Device, DeviceCapabilities, RxToken, TxToken};
use smoltcp::time::Instant;

pub struct SmolIxgbe {
    dev: Rc<RefCell<IxgbeDevice>>,
    ring_buffer: *mut IxgbeRingBuffer,
}

impl SmolIxgbe {
    pub fn new(dev: IxgbeDevice, ring_buffer: *mut IxgbeRingBuffer) -> Self {
        let boi = Self {
            ring_buffer,
            dev: Rc::new(RefCell::new(dev)),
        };

        boi
    }

    // do_rx() -> execute smoltcp functions -> do_tx()

    pub fn do_rx(&mut self) {
        let mut dev = (*self.dev).borrow_mut();
        let mut ring_buffer = unsafe { &mut *self.ring_buffer } ;

        dev.rx_submit_and_poll_with_ringbuffer_2(&mut ring_buffer.request_queue, &mut ring_buffer.request_completion_queue, false);
    }

    pub fn do_tx(&mut self) {
        let mut dev = (*self.dev).borrow_mut();
        let mut ring_buffer = unsafe { &mut *self.ring_buffer } ;

        dev.tx_submit_and_poll_with_ringbuffer_2(&mut ring_buffer.reply_queue, &mut ring_buffer.request_queue, false);
    }

    fn get_tx_token(&self) -> IxgbeTxToken {
        IxgbeTxToken {
            frame: None,
            ring_buffer: self.ring_buffer,
        }
    }
}

impl Device for SmolIxgbe {
    type RxToken<'a> = IxgbeRxToken;
    type TxToken<'a> = IxgbeTxToken;

    fn receive<'a>(&'a mut self, timestamp: Instant) -> Option<(Self::RxToken<'a>, Self::TxToken<'a>)> {
        // we are taking two buffers for each rx right now lol
        let mut ring_buffer = unsafe { &mut *self.ring_buffer };

        if let Some(pkt) = ring_buffer.request_completion_queue.try_pop() {
            //log::debug!("got packet");

            let rx_token = IxgbeRxToken {
                frame: Some(pkt),
                ring_buffer: self.ring_buffer,
            };
            let tx_token = self.get_tx_token();

            Some((rx_token, tx_token))
        } else {
            None
        }
    }

    fn transmit<'a>(&'a mut self, timestamp: Instant) -> Option<Self::TxToken<'a>> {
        Some(self.get_tx_token())
    }

    fn capabilities(&self) -> DeviceCapabilities {
        let mut cap = DeviceCapabilities::default();

        cap.max_transmission_unit = 2048;
        cap.max_burst_size = None;
        cap.checksum = ChecksumCapabilities::ignored();
        cap.checksum.ipv4 = Checksum::Tx;
        cap.checksum.tcp = Checksum::Tx;

        cap
    }
}

pub struct IxgbeTxToken {
    frame: Option<IxgbePayLoad>,
    ring_buffer: *mut IxgbeRingBuffer,
}

impl TxToken for IxgbeTxToken {
    fn consume<R, F>(mut self, len: usize, f: F) -> R
    where
        F: FnOnce(&mut [u8]) -> R,
    {
        let mut frame = if let Some(frame) = self.frame.take() {
            frame
        } else {
            let mut ring_buffer = unsafe { &mut *core::hint::black_box(self.ring_buffer) } ;

            if let Some(pkt) = ring_buffer.request_queue.try_pop() {
                //log::debug!("taking tx buffer");
                pkt
            } else if let Some((addr, paddr)) = ring_buffer.try_pop_allocator() {
                //panic!("no free buffer");
                IxgbePayLoad {
                    addr,
                    paddr,
                    len: 4096,
                }
            } else {
                panic!("Failed to allocate");
            }
        };

        //let mut frame = self.frame.take().expect("No frame available");
        frame.len = len;
        let slice = unsafe { slice::from_raw_parts_mut(frame.addr as *mut u8, frame.len) };

        let result = f(slice);

        let mut ring_buffer = unsafe { &mut *self.ring_buffer } ;
        ring_buffer.reply_queue.try_push(&frame);

        result
    }
}

impl Drop for IxgbeTxToken {
    fn drop(&mut self) {
        if let Some(frame) = self.frame.take() {
            //log::debug!("pushing tx back");
            let mut ring_buffer = unsafe { &mut *self.ring_buffer } ;
            ring_buffer.request_queue.try_push(&frame);
        }
    }
}

pub struct IxgbeRxToken {
    frame: Option<IxgbePayLoad>,
    ring_buffer: *mut IxgbeRingBuffer,
}

impl RxToken for IxgbeRxToken {
    fn consume<R, F>(mut self, f: F) -> R
    where
        F: FnOnce(&mut [u8]) -> R,
    {
        let mut frame = self.frame.take().expect("No frame available");
        let slice = unsafe { slice::from_raw_parts_mut(frame.addr as *mut u8, frame.len) };

        let result = f(slice);

        //log::debug!("pushing rx back");
        let mut ring_buffer = unsafe { &mut *self.ring_buffer } ;
        ring_buffer.request_queue.try_push(&frame);

        result
    }
}

impl Drop for IxgbeRxToken {
    fn drop(&mut self) {
        if let Some(frame) = self.frame.take() {
            //log::debug!("pushing rx back");
            let mut ring_buffer = unsafe { &mut *self.ring_buffer } ;
            ring_buffer.request_queue.try_push(&frame);
        }
    }
}
