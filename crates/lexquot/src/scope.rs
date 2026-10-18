use crate::ManyToOneIdMap;

pub fn complete_with_continuation_singletons(map: &mut ManyToOneIdMap) {
    for raw in 0..map.original_to_internal.len() {
        if map.original_to_internal[raw] != u32::MAX {
            continue;
        }
        let internal = map.internal_to_originals.len() as u32;
        map.original_to_internal[raw] = internal;
        map.internal_to_originals.push(vec![raw as u32]);
        map.representative_original_ids.push(raw as u32);
    }
}

pub fn restrict_quotient_to_initial_domain(
    quotient: &ManyToOneIdMap,
    domain: &ManyToOneIdMap,
) -> Option<ManyToOneIdMap> {
    let n = domain.original_to_internal.len();
    if quotient.original_to_internal.len() != n {
        return None;
    }
    let mut remap = vec![u32::MAX; quotient.num_internal_ids() as usize];
    let mut original_to_internal = vec![u32::MAX; n];
    let mut groups = Vec::<Vec<u32>>::new();
    let mut representatives = Vec::new();
    for (raw, &allowed) in domain.original_to_internal.iter().enumerate() {
        if allowed == u32::MAX {
            continue;
        }
        let class = quotient.original_to_internal[raw] as usize;
        let slot = remap.get_mut(class)?;
        if *slot == u32::MAX {
            *slot = groups.len() as u32;
            groups.push(Vec::new());
            representatives.push(raw as u32);
        }
        original_to_internal[raw] = *slot;
        groups[*slot as usize].push(raw as u32);
    }
    Some(ManyToOneIdMap {
        original_to_internal,
        internal_to_originals: groups,
        representative_original_ids: representatives,
    })
}
