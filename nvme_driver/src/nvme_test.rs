use crate::device::NvmeDevice;
use crate::println;
use crate::{BlockOp, BlockReq};
use alloc::collections::VecDeque;
use alloc::vec::Vec;
use b2histogram::Base2Histogram;
use libtime::rdtsc;
use libtime::sys_ns_loopsleep;

fn run_blocktest_raw(
    dev: &mut NvmeDevice,
    runtime: u64,
    batch_sz: u64,
    is_write: bool,
    is_random: bool,
) {
    run_blocktest_raw_with_delay(dev, runtime, batch_sz, is_write, is_random, 0);
}

pub fn run_blocktest_raw_with_delay(
    dev: &mut NvmeDevice,
    runtime: u64,
    batch_sz: u64,
    is_write: bool,
    is_random: bool,
    delay: u64,
) {
    let req: Vec<u8>;
    if is_write {
        req = alloc::vec![0xdeu8; 4096];
    } else {
        req = alloc::vec![0u8; 4096];
    }

    let mut submit: VecDeque<Vec<u8>> = VecDeque::with_capacity(batch_sz as usize);
    let mut collect: VecDeque<Vec<u8>> = VecDeque::new();

    let _block_num: u64 = 0;

    for _i in 0..batch_sz {
        let req1 = req.clone();
        //println!("req 0x{:08x}", req1.as_ptr() as u64);
        submit.push_back(req1);
    }

    /*println!(
        "submit ptr {:08x} collect ptr 0x{:08x}",
        &submit as *mut _ as *mut u64 as u64, &collect as *mut _ as *mut u64 as u64
    );*/
    //if let Some(device) = dev.as_mut() {
    //let dev: &mut NvmeDevice = device;

    let mut submit_start = 0;
    let mut submit_elapsed = 0;
    let _poll_start = 0;
    let _poll_elapsed = 0;
    let mut count = 0;
    let mut alloc_count = 0;

    let mut submit_hist = Base2Histogram::new();
    let mut poll_hist = Base2Histogram::new();
    let mut ret = 0;

    println!(
        "======== Starting {}{} test (delay {})  ==========",
        if is_random { "rand" } else { "" },
        if is_write { "write" } else { "read" },
        delay
    );

    let tsc_start = rdtsc();
    let tsc_end = tsc_start + runtime * 2_400_000_000;

    loop {
        count += 1;
        submit_start = rdtsc();
        //println!("submit and poll raw count {}", count);
        // {
        //  NVME
        //  &submit.vecdequeue()
        //  &collect.vecdequue()
        //  is_write
        //  is_random
        // }
        ret = dev.submit_and_poll_raw(&mut submit, &mut collect, is_write, is_random);

        submit_elapsed += rdtsc() - submit_start;

        submit_hist.record(ret as u64);

        poll_hist.record(collect.len() as u64);

        //println!("Append # {} finished blocks {}", count, collect.len());
        submit.append(&mut collect);

        if submit.is_empty() {
            alloc_count += 1;
            //println!("allocating new batch at count {}", count);
            for _i in 0..batch_sz {
                submit.push_back(req.clone());
            }
        }

        if rdtsc() > tsc_end {
            break;
        }
        sys_ns_loopsleep(delay);
    }

    let elapsed = rdtsc() - tsc_start;

    let adj_runtime = elapsed as f64 / 2_400_000_000_f64;

    let (sub, comp) = dev.stats.get_stats();

    println!("Polling ....");

    let done = dev.poll_raw(&mut collect);

    println!("Poll: Reaped {} requests", done);
    println!("submit {} requests", submit.len());
    println!("collect {} requests", collect.len());

    println!("runtime: {:.2} seconds", adj_runtime);
    println!("total sub {} comp {}", sub, comp);

    println!(
        "submitted {:.2} K IOPS completed {:.2} K IOPS",
        sub as f64 / adj_runtime as f64 / 1_000_f64,
        comp as f64 / adj_runtime as f64 / 1_000_f64
    );
    println!(
        "submit_and_poll_rref took {} cycles (avg {} cycles)",
        submit_elapsed,
        submit_elapsed / count
    );

    println!("Number of new allocations {}", alloc_count * batch_sz);

    for hist in alloc::vec![submit_hist, poll_hist] {
        println!("hist:");
        // Iterate buckets that have observations
        for bucket in hist.iter().filter(|b| b.count > 0) {
            println!("({:5}, {:5}): {}", bucket.start, bucket.end, bucket.count);
            println!("\n");
        }
    }
    println!("++++++++++++++++++++++++++++++++++++++++++++++++++++");
    //}
}

pub fn run_blocktest_blkreq(dev: &mut NvmeDevice) {
    let req: Vec<u8>;
    req = alloc::vec![0xdeu8; 4096];

    let mut block_num: u64 = 0;
    let batch_sz = 32;
    let runtime = 30;

    let mut submit: VecDeque<BlockReq> = VecDeque::with_capacity(batch_sz as usize);
    let mut collect: VecDeque<BlockReq> = VecDeque::new();

    for i in 0..32 {
        let mut breq = BlockReq::new(block_num, 8, req.clone().leak().as_ptr() as usize, BlockOp::Read);
        block_num = block_num.wrapping_add(8);
        submit.push_back(breq);
    }

    let mut submit_start = 0;
    let mut submit_elapsed = 0;

    let mut alloc_count = 0;
    let mut alloc_elapsed = 0;

    let mut count: u64 = 0;
    let mut total_requests = 0;

    let mut submit_hist = Base2Histogram::new();
    let mut poll_hist = Base2Histogram::new();
    let mut ret = 0;

    let tsc_start = rdtsc();
    let tsc_end = tsc_start + runtime * 2_400_000_000;

    loop {
        count += 1;
        submit_start = rdtsc();
        log::trace!("Calling submit_and_poll_breq");
        ret = dev.submit_and_poll_breq(&mut submit, &mut collect);
        submit_elapsed += rdtsc() - submit_start;

        //assert_eq!(ret, collect.len());
        total_requests += ret;

        log::trace!("submitted {} reqs, collect {} reqs ", ret, collect.len(),);
        submit_hist.record(ret as u64);

        poll_hist.record(collect.len() as u64);

        while let Some(mut breq) = collect.pop_front() {
            breq.block = block_num as u64;
            block_num = block_num.wrapping_add(8);
            submit.push_back(breq);
        }

        if submit.is_empty() {
            //&& (alloc_count * batch_sz) < 1024 {
            //println!("Alloc new batch at {}", count);
            alloc_count += 1;
            let alloc_rdstc_start = rdtsc();
            for i in 0..32 {
                let breq = BlockReq::new(block_num, 8, req.clone().leak().as_ptr() as usize, BlockOp::Read);
                block_num = block_num.wrapping_add(8);
                submit.push_back(breq);
            }
            alloc_elapsed += rdtsc() - alloc_rdstc_start;
        }

        if rdtsc() > tsc_end {
            break;
        }
        //sys_ns_loopsleep(2000);
    }

    let elapsed = rdtsc() - tsc_start;

    let adj_runtime = elapsed as f64 / 2_400_000_000_u64 as f64;

    let (sub, comp) = dev.stats.get_stats();

    // println!("Polling .... last_sq {} last_cq {} sq_id {}", last_sq, last_cq, sq_id);
    println!("Polling ....");

    let done = dev.poll_breq(&mut collect);

    println!("Poll: Reaped {} requests", done);
    println!("submit {} requests", submit.len());
    println!("collect {} requests", collect.len());
    println!("runtime: {:.2} seconds", adj_runtime);

    println!(
        "submitted {:.2} K IOPS completed {:.2} K IOPS",
        sub as f64 / adj_runtime as f64 / 1_000 as f64,
        comp as f64 / adj_runtime as f64 / 1_000 as f64
    );
    println!(
        "submit_and_poll_rref took {} cycles (avg {} cycles)",
        submit_elapsed,
        submit_elapsed / count
    );

    let bytes_sec = (total_requests * 4096) as f64 / adj_runtime;

    println!("Total Blocks: {}", total_requests);
    println!("Throughput: {} Bytes / sec", bytes_sec);
    println!("Throughput: {} KB / sec", bytes_sec / 1024 as f64);
    println!("Throughput: {} MB / sec", bytes_sec / (1024 * 1024) as f64);
    println!(
        "Throughput: {} GB / sec",
        bytes_sec / (1024 * 1024 * 1024) as f64
    );

    println!("Number of new allocations {}", alloc_count * batch_sz);

    for hist in alloc::vec![submit_hist, poll_hist] {
        println!("hist:");
        // Iterate buckets that have observations
        for bucket in hist.iter().filter(|b| b.count > 0) {
            println!("({:5}, {:5}): {}", bucket.start, bucket.end, bucket.count);
            println!("\n");
        }
    }
    println!("++++++++++++++++++++++++++++++++++++++++++++++++++++");
}
