#![forbid(unsafe_code)]

mod analysis;
mod cfg;

pub use analysis::{
    eliminate_dead_code, optimize, propagate_constants, simplify_block, simplify_exp, simplify_sub,
    to_ssa,
};
pub use cfg::{Cfg, PSEUDO_EXIT, PSEUDO_START};
