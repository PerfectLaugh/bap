use crate::model::{WEdge, WLive, WSub, WVar, sub_from_wire, sub_to_wire, var_from_wire};
use bap_cfg::{Cfg, PSEUDO_EXIT, PSEUDO_START};
use std::collections::{BTreeSet, LinkedList};

const START_ID: isize = -1;
const EXIT_ID: isize = -2;

#[ocaml::func]
pub fn bap_cfg_rs_ssa(input: WSub) -> Result<WSub, String> {
    Ok(sub_to_wire(&bap_cfg::to_ssa(&sub_from_wire(&input))))
}

fn destination(jmp: &bap_bir::Jmp) -> Option<u64> {
    match &jmp.kind {
        bap_bir::JmpKind::Goto(bap_bir::Label::Direct(tid))
        | bap_bir::JmpKind::Return(bap_bir::Label::Direct(tid)) => Some(*tid),
        bap_bir::JmpKind::Call {
            return_to: Some(bap_bir::Label::Direct(tid)),
            ..
        } => Some(*tid),
        bap_bir::JmpKind::Interrupt { return_to, .. } => Some(*return_to),
        _ => None,
    }
}
fn output_tid(tid: u64) -> isize {
    match tid {
        PSEUDO_START => START_ID,
        PSEUDO_EXIT => EXIT_ID,
        tid => tid as isize,
    }
}

#[ocaml::func]
pub fn bap_cfg_rs_edges(input: WSub, connected: bool) -> Result<LinkedList<WEdge>, String> {
    let sub = sub_from_wire(&input);
    let cfg = if connected {
        Cfg::connected(&sub)
    } else {
        Cfg::from_sub(&sub)
    };
    let edges = cfg.edges.iter().flat_map(|(source, targets)| {
        let block = &cfg.blocks[source];
        targets.iter().flat_map(move |target| {
            let labels = block
                .jmps
                .iter()
                .filter(|jmp| destination(jmp) == Some(*target))
                .map(|jmp| jmp.tid)
                .collect::<Vec<_>>();
            let labels = if labels.is_empty() {
                vec![*source]
            } else {
                labels
            };
            labels.into_iter().map(move |label| WEdge {
                src: output_tid(*source),
                dst: output_tid(*target),
                label: output_tid(label),
            })
        })
    });
    Ok(edges.collect())
}

#[ocaml::func]
pub fn bap_cfg_rs_liveness(
    input: WSub,
    keep: LinkedList<WVar>,
) -> Result<LinkedList<WLive>, String> {
    let sub = sub_from_wire(&input);
    let keep = keep.iter().map(var_from_wire).collect::<BTreeSet<_>>();
    let cfg = Cfg::connected(&sub);
    let (ins, outs) = cfg.liveness_from(PSEUDO_EXIT, keep);
    let reports = cfg.blocks.keys().map(|tid| WLive {
        tid: output_tid(*tid),
        ins: ins
            .get(tid)
            .unwrap_or(&Default::default())
            .iter()
            .map(crate::model::var_to_wire)
            .collect(),
        outs: outs
            .get(tid)
            .unwrap_or(&Default::default())
            .iter()
            .map(crate::model::var_to_wire)
            .collect(),
    });
    Ok(reports.collect())
}
