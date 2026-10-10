//! Shared legacy diagnostic guards; not a stable public policy API.
use std::cell::Cell;
thread_local! { pub static VOCAB_INPLACE_DISALLOWED_INTERSECTION_SUPPRESS_DEPTH: Cell<u32> = const { Cell::new(0) }; }
pub fn vocab_inplace_disallowed_intersection_enabled() -> bool {
 VOCAB_INPLACE_DISALLOWED_INTERSECTION_SUPPRESS_DEPTH.with(|d| d.get()==0) && std::env::var("LEXQUOT_VOCAB_INPLACE_DISALLOWED_INTERSECTION")
 .map(|v| !matches!(v.trim().to_ascii_lowercase().as_str(), "" | "0" | "false" | "no" | "off")).unwrap_or(true)
}
thread_local! { pub static VOCAB_REUSE_DENSE_DISALLOWED_SLOTS_SUPPRESS_DEPTH: Cell<u32> = const { Cell::new(0) }; }
pub fn vocab_reuse_dense_disallowed_slots_enabled() -> bool {
 VOCAB_REUSE_DENSE_DISALLOWED_SLOTS_SUPPRESS_DEPTH.with(|d| d.get()==0) && std::env::var("LEXQUOT_VOCAB_REUSE_DENSE_DISALLOWED_SLOTS")
 .map(|v| !matches!(v.trim().to_ascii_lowercase().as_str(), "" | "0" | "false" | "no" | "off")).unwrap_or(true)
}
thread_local! { pub static VOCAB_REUSE_SINGLE_TARGET_DISALLOWED_SUPPRESS_DEPTH: Cell<u32> = const { Cell::new(0) }; }
pub fn vocab_reuse_single_target_disallowed_enabled() -> bool {
 VOCAB_REUSE_SINGLE_TARGET_DISALLOWED_SUPPRESS_DEPTH.with(|d| d.get()==0) && std::env::var("LEXQUOT_VOCAB_REUSE_SINGLE_TARGET_DISALLOWED")
 .map(|v| !matches!(v.trim().to_ascii_lowercase().as_str(), "" | "0" | "false" | "no" | "off")).unwrap_or(true)
}

thread_local! { pub static FIRST_BYTE_VOCAB_FACTOR_SUPPRESS_DEPTH: Cell<u32> = const { Cell::new(0) }; }

thread_local! { pub static LOCAL_SHARED_EQUIV_BASE_SUPPRESS_DEPTH: Cell<u32> = const { Cell::new(0) }; }

thread_local! { pub static TERMINAL_INTERCHANGEABILITY_STRICT_REFERENCE_SUPPRESS_DEPTH: Cell<u32> = const { Cell::new(0) }; }

pub fn l2p_env_enabled(name: &str) -> bool {
    std::env::var(name)
        .map(|value| {
            let value = value.trim();
            !value.is_empty() && value != "0" && !value.eq_ignore_ascii_case("false")
        })
        .unwrap_or(false)
}

pub fn l2p_partition_selector_enabled(name: &str, partition_label: &str) -> bool {
    std::env::var(name)
        .map(|value| {
            let trimmed = value.trim();
            if trimmed.is_empty() || trimmed == "1" || trimmed.eq_ignore_ascii_case("true") {
                return true;
            }
            if trimmed == "0" || trimmed.eq_ignore_ascii_case("false") {
                return false;
            }
            trimmed
                .split(',')
                .map(str::trim)
                .any(|label| label == partition_label)
        })
        .unwrap_or(false)
}

pub fn l2p_first_byte_vocab_factor_enabled_for_partition(
    partition_label: &str,
) -> bool {
    if FIRST_BYTE_VOCAB_FACTOR_SUPPRESS_DEPTH.with(|depth| depth.get() != 0) {
        return false;
    }
    if std::env::var_os("LEXQUOT_ENABLE_L2P_FIRST_BYTE_VOCAB_FACTOR").is_none()
        && partition_label.starts_with("boundary_shard")
    {
        // Static-link boundary shards factor the full 128k-vocabulary
        // equivalence internally (5.0M source-state buckets -> 143k, vocab
        // 3.9s -> 0.9s, exact-state 1.9s -> 0.6s on selected10) with no input
        // narrowing: the factored classes are validated against the full
        // exact partition by the factor strict-reference mode, and the
        // selected10 oracle gate pins the 143-token output. An explicit env
        // setting still overrides this default for diagnostics.
        return true;
    }
    l2p_partition_selector_enabled(
        "LEXQUOT_ENABLE_L2P_FIRST_BYTE_VOCAB_FACTOR",
        partition_label,
    )
}

pub fn l2p_first_byte_vocab_factor_strict_reference_enabled_for_partition(
    partition_label: &str,
) -> bool {
    l2p_first_byte_vocab_factor_enabled_for_partition(partition_label)
        && l2p_partition_selector_enabled(
            "LEXQUOT_L2P_FIRST_BYTE_VOCAB_FACTOR_STRICT_REFERENCE",
            partition_label,
        )
}

pub fn p8_first_byte_factorization_allowed() -> bool {
    // Forced-all-L2P is a diagnostic route that does not preserve the normal
    // classifier invariants of the structural-boundary partition.
    !l2p_env_enabled("LEXQUOT_FORCE_ALL_L2P")
}

pub fn l2p_terminal_interchangeability_strict_reference_enabled() -> bool {
    TERMINAL_INTERCHANGEABILITY_STRICT_REFERENCE_SUPPRESS_DEPTH.with(|depth| depth.get() == 0)
        && l2p_env_enabled("LEXQUOT_L2P_TERMINAL_INTERCHANGEABILITY_STRICT_REFERENCE")
}

pub fn local_shared_equiv_base_enabled() -> bool {
    LOCAL_SHARED_EQUIV_BASE_SUPPRESS_DEPTH.with(|depth| depth.get() == 0)
        && std::env::var_os("LEXQUOT_DISABLE_L2P_LOCAL_SHARED_EQUIV_BASE").is_none()
}
