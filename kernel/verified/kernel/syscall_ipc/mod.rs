pub mod syscall_receive;
pub mod syscall_reply;
pub mod syscall_reply_and_receive;
pub mod syscall_send;
pub mod syscall_send_empty;
pub mod syscall_send_pages;

pub use syscall_receive::*;
pub use syscall_reply::*;
pub use syscall_reply_and_receive::*;
pub use syscall_send::*;
pub use syscall_send_empty::*;
pub use syscall_send_pages::*;
