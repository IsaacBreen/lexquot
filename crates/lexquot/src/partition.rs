//! Explicit local analysis families and exact common refinement.
//!
//! Routing a token through L1 rather than L2P requires a consumer-side proof.
//! This module never guesses that proof from token length or byte shape.
use std::collections::BTreeSet;
use crate::{Analysis,AnalysisError,AnalysisRequest,Backend,Budget,ManyToOneIdMap,Observation,Tokenizer,Vocab,refine_token_partitions};

#[derive(Debug,Clone)]
pub struct PartitionSpec {
    name:String,
    observation:Observation,
    token_ids:Vec<u32>,
    initial_states:Option<Vec<u32>>,
    terminals:Option<Vec<u32>>,
    follows:Vec<(u32,u32)>,
}
impl PartitionSpec {
    pub fn new(name:impl Into<String>,observation:Observation,tokens:impl IntoIterator<Item=u32>)->Self {
        Self{name:name.into(),observation,token_ids:tokens.into_iter().collect(),initial_states:None,terminals:None,follows:Vec::new()}
    }
    pub fn initial_states(mut self,states:impl IntoIterator<Item=u32>)->Self {self.initial_states=Some(states.into_iter().collect());self}
    pub fn terminals(mut self,terminals:impl IntoIterator<Item=u32>)->Self {self.terminals=Some(terminals.into_iter().collect());self}
    pub fn forbidden_follows(mut self,pairs:impl IntoIterator<Item=(u32,u32)>)->Self {self.follows=pairs.into_iter().collect();self}
}

/// Each family retains its own initial-state map. There is deliberately no
/// unqualified global state quotient assembled from unrelated local classes.
pub struct PartitionedAnalysis {
    parts:Vec<Analysis>,
    token_map:ManyToOneIdMap,
}
impl PartitionedAnalysis {
    pub fn parts(&self)->&[Analysis] {&self.parts}
    pub fn token_map(&self)->&ManyToOneIdMap {&self.token_map}
}

pub struct PartitionedRequest<'a> {
    lexer:&'a Tokenizer,
    vocab:&'a Vocab,
    specs:Vec<PartitionSpec>,
    backend:Backend,
    budget:Budget,
    verify:bool,
}
impl<'a> PartitionedRequest<'a> {
    pub fn new(lexer:&'a Tokenizer,vocab:&'a Vocab)->Self {
        Self{lexer,vocab,specs:Vec::new(),backend:Backend::Auto,budget:Budget::default(),verify:false}
    }
    pub fn partition(mut self,spec:PartitionSpec)->Self {self.specs.push(spec);self}
    pub fn backend(mut self,backend:Backend)->Self {self.backend=backend;self}
    /// Per-family budget. The number of requested families is controlled by
    /// the caller; this is not a global allocator reservation.
    pub fn budget(mut self,budget:Budget)->Self {self.budget=budget;self}
    pub fn verify(mut self,verify:bool)->Self {self.verify=verify;self}
    pub fn analyze(self)->Result<PartitionedAnalysis,AnalysisError> {
        let mut names=BTreeSet::new();
        let mut coverage=BTreeSet::new();
        for spec in &self.specs {
            if spec.name.is_empty()||!names.insert(spec.name.clone()) {
                return Err(AnalysisError::InvalidInput("partition names must be nonempty and unique".into()));
            }
            for &token in &spec.token_ids {
                if !self.vocab.entries_map().contains_key(&token) {
                    return Err(AnalysisError::InvalidInput(format!("partition {} includes unknown or non-byte token {token}",spec.name)));
                }
                coverage.insert(token);
            }
        }
        if let Some(token)=self.vocab.entries_map().keys().find(|token|!coverage.contains(token)) {
            return Err(AnalysisError::InvalidInput(format!("byte token {token} has no analysis family")));
        }
        let mut parts=Vec::with_capacity(self.specs.len());
        for mut spec in self.specs {
            spec.token_ids.sort_unstable();spec.token_ids.dedup();
            let entries=spec.token_ids.iter().map(|&id|(id,self.vocab.entries_map()[&id].clone())).collect();
            let vocabulary=Vocab::new(entries);
            let mut request=AnalysisRequest::new(self.lexer,&vocabulary,spec.observation)
                .name(spec.name).backend(self.backend).budget(self.budget).verify(self.verify)
                .forbidden_follows(spec.follows);
            if let Some(states)=spec.initial_states {request=request.initial_states(states);}
            if let Some(terminals)=spec.terminals {request=request.terminals(terminals);}
            parts.push(request.analyze()?);
        }
        let token_ids=self.vocab.entries_map().keys().copied().collect::<Vec<_>>();
        let token_map=refine_token_partitions(&token_ids,&parts)?;
        Ok(PartitionedAnalysis{parts,token_map})
    }
}
