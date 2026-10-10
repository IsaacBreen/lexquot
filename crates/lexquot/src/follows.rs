use std::collections::BTreeMap;
use crate::ds::bitset::BitSet;
type TerminalID = u32;

pub fn ignore_transparent_disallowed_follows(
    disallowed_follows: &BTreeMap<u32, BitSet>,
    ignore_terminal: Option<TerminalID>,
) -> BTreeMap<u32, BitSet> {
    let Some(ignore_terminal) = ignore_terminal else {
        return disallowed_follows.clone();
    };

    let mut adjusted = disallowed_follows.clone();
    adjusted.remove(&ignore_terminal);
    for bits in adjusted.values_mut() {
        if (ignore_terminal as usize) < bits.len() {
            bits.clear(ignore_terminal as usize);
        }
    }
    adjusted.retain(|_, bits| !bits.is_zero());
    adjusted
}
