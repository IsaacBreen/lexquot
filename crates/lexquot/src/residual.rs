//! Direct single-terminal residual analysis without a combined lexer.
//!
//! Every represented DFA state is live for one terminal. An absent transition
//! is the implicit dead sink. Terminal identity belongs to the root relation,
//! not the automaton state, allowing equivalent residuals to share structure.
use std::collections::{BTreeMap,BTreeSet,HashMap};
use std::time::Instant;
use crate::{Vocab,InternalIdMap,Analysis,AnalysisError,AnalysisStats,Assurance,Budget,Domain,Observation};
use crate::api::{check_limit,map_from_classes};

/// Deterministic prefix-residual automaton. All states are live/accepting;
/// omitted byte transitions lead to a single implicit dead sink.
#[derive(Debug,Clone)]
pub struct ResidualDfa { transitions:Vec<Vec<(u8,u32)>> }
impl ResidualDfa {
    pub fn new(mut transitions:Vec<Vec<(u8,u32)>>)->Result<Self,AnalysisError> {
        let states=transitions.len();
        if states>u32::MAX as usize {return Err(AnalysisError::InvalidInput("too many residual states".into()));}
        for row in &mut transitions {
            row.sort_unstable();
            if row.windows(2).any(|p|p[0].0==p[1].0) {
                return Err(AnalysisError::InvalidInput("duplicate byte transition in residual DFA".into()));
            }
            if row.iter().any(|&(_,target)|target as usize>=states) {
                return Err(AnalysisError::InvalidInput("residual target outside DFA".into()));
            }
        }
        Ok(Self{transitions})
    }
    pub fn state_count(&self)->usize {self.transitions.len()}
    pub fn transitions(&self)->&[Vec<(u8,u32)>] {&self.transitions}

    /// Project one terminal from a deterministic lexer DFA. Returns the raw
    /// terminal-DFA-state to live-residual map; `None` marks a dead residual.
    /// Epsilon transitions are not supported by this constructor.
    pub fn from_terminal_dfa(dfa:&crate::DFA,terminal:u32)->Result<(Self,Vec<Option<u32>>),AnalysisError> {
        if dfa.has_epsilon_transitions() {
            return Err(AnalysisError::InvalidInput("project epsilon closures before importing a terminal residual DFA".into()));
        }
        let mut map=vec![None;dfa.num_states()];
        let mut count=0u32;
        for state in 0..dfa.num_states() as u32 {
            if dfa.finalizers(state).contains(terminal as usize)
                || dfa.possible_future_group_ids(state).contains(terminal as usize) {
                map[state as usize]=Some(count);count+=1;
            }
        }
        let mut transitions=vec![Vec::new();count as usize];
        for state in 0..dfa.num_states() as u32 {
            if let Some(source)=map[state as usize] {
                for (byte,target) in dfa.transitions(state) {
                    if let Some(target)=map[target as usize] {transitions[source as usize].push((byte,target));}
                }
            }
        }
        Ok((Self::new(transitions)?,map))
    }
}

/// One membership in the projection from an original lexer start and terminal
/// to a local residual. Several memberships for the same `(state,terminal)`
/// mean an existential union, as for projected epsilon-closed configurations.
#[derive(Debug,Clone,Copy,PartialEq,Eq)]
pub struct ProjectedRoot {
    pub original_state:u32,
    pub terminal:u32,
    pub machine:usize,
    pub residual_state:u32,
}

#[derive(Debug,Clone,Default)]
pub struct ResidualStats {
    pub source_states:usize,
    pub minimized_states:usize,
    pub root_vectors:usize,
    pub reverse_states:usize,
    pub reverse_transitions:usize,
    pub predecessor_visits:usize,
    pub minimize_ms:f64,
    pub reverse_ms:f64,
    pub reconstruction_ms:f64,
}
pub struct ResidualAnalysis {
    pub analysis:Analysis,
    pub residual_stats:ResidualStats,
}

/// Reusable projection harvested from a lexer compiler's retained coordinate
/// certificate, rather than inferred by rescanning all vocabulary tokens.
pub struct PreparedResiduals {
    pub machines: Vec<ResidualDfa>,
    pub roots: Vec<ProjectedRoot>,
    original_state_count: u32,
}
impl PreparedResiduals {
    pub fn from_lexer(lexer: &crate::Tokenizer) -> Result<Self,AnalysisError> {
        use crate::Lexer;
        let coordinates=lexer.terminal_residual_coordinates()
            .ok_or_else(||AnalysisError::InvalidInput("lexer has no retained terminal-residual coordinate certificate".into()))?;
        let mut machines=Vec::new();
        let mut maps=Vec::new();
        for terminal in 0..coordinates.terminal_dfa_count() as u32 {
            let (dfa,group)=coordinates.terminal_dfa_and_group(terminal)
                .ok_or_else(||AnalysisError::InvalidInput("missing terminal DFA in coordinate certificate".into()))?;
            let (machine,map)=ResidualDfa::from_terminal_dfa(dfa,group)?;
            machines.push(machine);maps.push(map);
        }
        let closures=lexer.all_singleton_epsilon_closures();
        let mut roots=Vec::new();
        for raw in 0..lexer.num_states() {
            let mut local=BTreeSet::new();
            for &source in &closures[raw as usize] {
                for &(terminal,residual) in coordinates.row(source)
                    .ok_or_else(||AnalysisError::InvalidInput("coordinate certificate does not cover a raw state".into()))? {
                    let mapped=maps.get(terminal as usize).and_then(|m|m.get(residual as usize))
                        .ok_or_else(||AnalysisError::InvalidInput("coordinate certificate points outside a terminal DFA".into()))?;
                    if let Some(residual)=mapped {local.insert((terminal,*residual));}
                }
            }
            roots.extend(local.into_iter().map(|(terminal,residual_state)|ProjectedRoot {
                original_state:raw,terminal,machine:terminal as usize,residual_state,
            }));
        }
        Ok(Self{machines,roots,original_state_count:lexer.num_states()})
    }
    pub fn request<'a>(&'a self,vocab:&'a Vocab)->ResidualRequest<'a> {
        ResidualRequest::new(&self.machines,&self.roots,vocab).initial_states(0..self.original_state_count)
    }
}
pub(crate) struct SurvivorColumns {
    pub state_classes:Vec<u32>,
    pub token_subsets:Vec<usize>,
    pub subsets:Vec<std::sync::Arc<[u64]>>,
    pub stats:ResidualStats,
}

/// Analyze a union of already-projected one-terminal residual machines.
/// No full multi-terminal DFA, parser, or weighted automaton is constructed.
pub struct ResidualRequest<'a> {
    machines:&'a [ResidualDfa], roots:&'a [ProjectedRoot], vocab:&'a Vocab,
    initial_states:Option<Vec<u32>>, budget:Budget, minimize:bool, name:String,
}
impl<'a> ResidualRequest<'a> {
    pub fn new(machines:&'a [ResidualDfa],roots:&'a [ProjectedRoot],vocab:&'a Vocab)->Self {
        Self{machines,roots,vocab,initial_states:None,budget:Budget::default(),minimize:true,name:"projected-residuals".into()}
    }
    pub fn initial_states(mut self,states:impl IntoIterator<Item=u32>)->Self {self.initial_states=Some(states.into_iter().collect());self}
    pub fn budget(mut self,budget:Budget)->Self {self.budget=budget;self}
    pub fn minimize(mut self,minimize:bool)->Self {self.minimize=minimize;self}
    pub fn name(mut self,name:impl Into<String>)->Self {self.name=name.into();self}

    pub fn analyze(self)->Result<ResidualAnalysis,AnalysisError> {
        let started=Instant::now();
        let mut initial_states=self.initial_states.unwrap_or_else(||self.roots.iter().map(|r|r.original_state).collect());
        initial_states.sort_unstable();initial_states.dedup();
        let raw_size=initial_states.last().map_or(0,|&s|s as u64+1);
        check_limit("residual initial-state map",raw_size,self.budget.max_map_entries as u64)?;
        let total_states=self.machines.iter().try_fold(0usize,|n,m|n.checked_add(m.state_count()))
            .ok_or(AnalysisError::InvalidInput("residual union size overflow".into()))?;
        check_limit("residual union states",total_states as u64,self.budget.max_map_entries as u64)?;
        check_limit("u32 residual coordinates",total_states as u64,u32::MAX as u64)?;
        let mut offsets=Vec::with_capacity(self.machines.len());
        let mut transitions=Vec::with_capacity(total_states);
        for machine in self.machines {
            let base=transitions.len() as u32;offsets.push(base);
            transitions.extend(machine.transitions.iter().map(|row|row.iter().map(|&(b,t)|(b,t+base)).collect::<Vec<_>>()));
        }
        for root in self.roots {
            if self.machines.get(root.machine).is_none_or(|m|root.residual_state as usize>=m.state_count()) {
                return Err(AnalysisError::InvalidInput("projected root points outside its residual DFA".into()));
            }
        }
        let tokens=self.vocab.entries_map().values().map(Vec::as_slice).collect::<Vec<_>>();
        let token_ids=self.vocab.entries_map().keys().copied().collect::<Vec<_>>();
        let token_size=token_ids.last().map_or(0,|&t|t as u64+1);
        check_limit("residual token map",token_size,self.budget.max_map_entries as u64)?;
        for token in &tokens {
            if token.is_empty(){return Err(AnalysisError::InvalidInput("empty byte token in residual query".into()));}
            check_limit("residual token bytes",token.len() as u64,self.budget.max_token_bytes as u64)?;
        }
        let columns=crate::l1::external_survivor_columns(&transitions,&tokens,self.minimize,self.budget)?;
        let reconstruction=Instant::now();
        let mut roots=BTreeMap::<u32,BTreeMap<u32,Vec<u32>>>::new();
        let allowed=initial_states.iter().copied().collect::<BTreeSet<_>>();
        for root in self.roots {
            if !allowed.contains(&root.original_state){continue;}
            let union_state=offsets[root.machine]+root.residual_state;
            roots.entry(root.original_state).or_default().entry(root.terminal).or_default()
                .push(columns.state_classes[union_state as usize]);
        }
        type RootVector=Vec<(u32,Vec<u32>)>;
        let mut vectors=Vec::<RootVector>::new();
        let mut vector_ids=HashMap::<RootVector,usize>::new();
        let raw_vectors=initial_states.iter().map(|&raw| {
            let row=roots.remove(&raw).unwrap_or_default().into_iter().map(|(t,mut states)|{
                states.sort_unstable();states.dedup();(t,states)
            }).collect::<Vec<_>>();
            let next=vectors.len();
            *vector_ids.entry(row.clone()).or_insert_with(||{vectors.push(row);next})
        }).collect::<Vec<_>>();
        let cells=vectors.len().saturating_mul(columns.subsets.len());
        check_limit("projected observation cells",cells as u64,self.budget.max_table_cells as u64)?;
        let mut observations=HashMap::<Vec<u32>,u32>::new();
        let rows=vectors.iter().map(|row| {
            columns.subsets.iter().map(|set| {
                let live=row.iter().filter(|(_,states)|states.iter().any(|&s|set[s as usize/64]&(1u64<<(s%64))!=0))
                    .map(|&(t,_)|t).collect::<Vec<_>>();
                let next=observations.len() as u32;*observations.entry(live).or_insert(next)
            }).collect::<Vec<_>>()
        }).collect::<Vec<_>>();
        let mut row_ids=HashMap::<Vec<u32>,u32>::new();
        let vector_classes=rows.iter().map(|row|{let next=row_ids.len() as u32;*row_ids.entry(row.clone()).or_insert(next)}).collect::<Vec<_>>();
        let state_classes=raw_vectors.iter().map(|&v|vector_classes[v]).collect::<Vec<_>>();
        let mut column_ids=HashMap::<Vec<u32>,u32>::new();
        let subset_classes=(0..columns.subsets.len()).map(|subset|{
            let key=rows.iter().map(|row|row[subset]).collect::<Vec<_>>();
            let next=column_ids.len() as u32;*column_ids.entry(key).or_insert(next)
        }).collect::<Vec<_>>();
        let token_classes=columns.token_subsets.iter().map(|&s|subset_classes[s]).collect::<Vec<_>>();
        let mut stats=columns.stats;
        stats.root_vectors=vectors.len();stats.reconstruction_ms=reconstruction.elapsed().as_secs_f64()*1000.0;
        let terminal_ids=self.roots.iter().filter(|r|allowed.contains(&r.original_state)).map(|r|r.terminal).collect::<BTreeSet<_>>().into_iter().collect();
        let analysis=Analysis {
            domain:Domain{name:self.name,observation:Observation::L1,initial_states:initial_states.clone(),token_ids:token_ids.clone(),terminal_ids},
            maps:InternalIdMap {
                tokenizer_states:map_from_classes(raw_size as usize,&initial_states,&state_classes),
                vocab_tokens:map_from_classes(token_size as usize,&token_ids,&token_classes),
                deferred_vocab_singleton_original_ids:None,
            },
            assurance:Assurance::ExactObservation,
            stats:AnalysisStats{total_ms:started.elapsed().as_secs_f64()*1000.0,table_cells:cells,byte_steps:stats.predecessor_visits as u64,..Default::default()},
        };
        Ok(ResidualAnalysis{analysis,residual_stats:stats})
    }
}
