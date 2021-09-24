/// `CacheError` is the errors of lfu module.
#[derive(Debug)]
pub enum CacheError {
    ///
    BadWidth(u64),
    ///
    InvalidParams,
}
