# Justification Theory

## 📋 Overview

Justification Theory is a core branch of epistemology that studies the rationality criteria and justification conditions for beliefs. Justification is a key element in the constitution of knowledge, exploring how to distinguish rational from irrational beliefs, as well as the nature, sources, and structure of justification.

## 🎯 Core Objectives

1. **Justification Nature Analysis**: Explore the essence and properties of justification
2. **Justification Sources Research**: Analyze different sources and foundations of justification
3. **Justification Structure Theory**: Study the structure and organization of justification
4. **Justification Standards Establishment**: Establish normative standards for evaluating justification

## 📚 Contents

- [Justification Theory](#justification-theory)
  - [📋 Overview](#-overview)
  - [🎯 Core Objectives](#-core-objectives)
  - [📚 Contents](#-contents)
  - [1. Basic Concepts](#1-basic-concepts)
    - [1.1 Definition of Justification](#11-definition-of-justification)
    - [1.2 Basic Properties of Justification](#12-basic-properties-of-justification)
    - [1.3 Justification Types](#13-justification-types)
      - [1.3.1 Classification by Source](#131-classification-by-source)
      - [1.3.2 Classification by Structure](#132-classification-by-structure)
  - [2. Formal Definitions](#2-formal-definitions)
    - [2.1 Justification Logic Foundations](#21-justification-logic-foundations)
    - [2.2 Justification Models](#22-justification-models)
    - [2.3 Justification Semantics](#23-justification-semantics)
    - [2.4 Justification Axiom System](#24-justification-axiom-system)
  - [3. Theorems and Proofs](#3-theorems-and-proofs)
    - [3.1 Justification Transmission Theorem](#31-justification-transmission-theorem)
    - [3.2 Justification Accumulation Theorem](#32-justification-accumulation-theorem)
    - [3.3 Justification Reflection Theorem](#33-justification-reflection-theorem)
  - [4. Code Implementation](#4-code-implementation)
    - [4.1 Justification Logic Implementation (Rust)](#41-justification-logic-implementation-rust)
  - [5. Application Examples](#5-application-examples)
    - [5.1 Scientific Method](#51-scientific-method)
    - [5.2 Legal Reasoning](#52-legal-reasoning)
    - [5.3 AI Expert Systems](#53-ai-expert-systems)
  - [6. Related Theories](#6-related-theories)
  - [7. References](#7-references)

## 1. Basic Concepts

### 1.1 Definition of Justification

**Justification** is the process or state that rationalizes a belief, providing sufficient reason for supporting it.

**Formal Definition**:
Let $A$ be a subject, $p$ a proposition, and $J$ a justification relation, then:
$$J(A, p) \iff A \text{ has sufficient justification for } p$$

### 1.2 Basic Properties of Justification

1. **Normativity**: Justification has normative characteristics
2. **Transmissibility**: Justification can be transmitted between beliefs
3. **Cumulativity**: Multiple justifications can accumulate
4. **Defeasibility**: Justification can be defeated by new evidence

### 1.3 Justification Types

#### 1.3.1 Classification by Source

- **Empirical Justification**: Based on perceptual experience
- **Rational Justification**: Based on rational reasoning
- **Authoritative Justification**: Based on authoritative sources
- **Intuitive Justification**: Based on intuition

#### 1.3.2 Classification by Structure

- **Foundational Justification**: Not dependent on other beliefs
- **Inferential Justification**: Dependent on other beliefs
- **Coherential Justification**: Based on coherence of belief system

## 2. Formal Definitions

### 2.1 Justification Logic Foundations

**Justification Logic Language** $\mathcal{L}_{Just}$:

$$\mathcal{L}_{Just} = \mathcal{L}_0 \cup \{Just_i \mid i \in Ag\} \cup \{t: \phi \mid t \in Term, \phi \in \mathcal{L}_{Just}\}$$

where $Term$ is the set of justification terms.

### 2.2 Justification Models

**Justification Model** $M = \langle W, R, E, V \rangle$:

- $W$: Set of possible worlds
- $R: Ag \rightarrow 2^{W \times W}$: Accessibility relation
- $E: W \times Term \rightarrow 2^{\mathcal{L}_{Just}}$: Evidence function
- $V: Prop \rightarrow 2^W$: Valuation function

### 2.3 Justification Semantics

For any $w \in W$ and formula $\phi$:

$$M, w \models t: \phi \iff \phi \in E(w, t) \text{ and } \forall v \in W: (w, v) \in R \Rightarrow M, v \models \phi$$

### 2.4 Justification Axiom System

**LP Axiom System**:

1. **A1**: $t: \phi \rightarrow \phi$ (Factivity)
2. **A2**: $t: (\phi \rightarrow \psi) \rightarrow (s: \phi \rightarrow (t \cdot s): \psi)$ (Application)
3. **A3**: $t: \phi \rightarrow !t: (t: \phi)$ (Positive Introspection)
4. **A4**: $t: \phi \vee s: \phi \rightarrow (t + s): \phi$ (Sum)

## 3. Theorems and Proofs

### 3.1 Justification Transmission Theorem

**Theorem**: If subject $A$ has justification for $p \rightarrow q$ and has justification for $p$, then $A$ has justification for $q$.

**Proof**:

1. Assume $Just(A, p \rightarrow q)$ and $Just(A, p)$
2. By justification logic axiom A2: $t: (\phi \rightarrow \psi) \rightarrow (s: \phi \rightarrow (t \cdot s): \psi)$
3. Applying modus ponens, we get $Just(A, q)$

### 3.2 Justification Accumulation Theorem

**Theorem**: If subject $A$ has justification $t$ for $p$ and justification $s$ for $p$, then $A$ has justification $t + s$ for $p$.

**Proof**:

1. Assume $t: p$ and $s: p$
2. By justification logic axiom A4: $t: \phi \vee s: \phi \rightarrow (t + s): \phi$
3. Directly, we get $(t + s): p$

### 3.3 Justification Reflection Theorem

**Theorem**: If subject $A$ has justification $t$ for $p$, then $A$ has justification for having justification $t$ for $p$.

**Proof**:

1. Assume $t: p$
2. By justification logic axiom A3: $t: \phi \rightarrow !t: (t: \phi)$
3. Directly, we get $!t: (t: p)$

## 4. Code Implementation

### 4.1 Justification Logic Implementation (Rust)

```rust
use std::collections::HashMap;

/// Justification Logic System
pub struct JustificationSystem {
    agents: Vec<String>,
    justifications: HashMap<String, HashMap<Proposition, Vec<JustificationTerm>>>,
    evidence_base: HashMap<JustificationTerm, Evidence>,
    world_states: Vec<WorldState>,
}

/// Justification Term
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum JustificationTerm {
    Constant(String),
    Variable(String),
    Application(Box<JustificationTerm>, Box<JustificationTerm>),
    Sum(Box<JustificationTerm>, Box<JustificationTerm>),
    Factorial(Box<JustificationTerm>),
}

/// Evidence
#[derive(Debug, Clone)]
pub struct Evidence {
    term: JustificationTerm,
    propositions: Vec<Proposition>,
    strength: f64,
    source: EvidenceSource,
}

/// Evidence Source
#[derive(Debug, Clone)]
pub enum EvidenceSource {
    Perception,
    Reasoning,
    Authority,
    Intuition,
    Testimony,
}

/// Proposition
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Proposition {
    Atomic(String),
    Not(Box<Proposition>),
    And(Box<Proposition>, Box<Proposition>),
    Or(Box<Proposition>, Box<Proposition>),
    Implies(Box<Proposition>, Box<Proposition>),
    Justified(String, JustificationTerm, Box<Proposition>),
}

/// World State
#[derive(Debug, Clone)]
pub struct WorldState {
    id: String,
    propositions: HashMap<String, bool>,
}

impl JustificationSystem {
    /// Create a new justification system
    pub fn new() -> Self {
        Self {
            agents: Vec::new(),
            justifications: HashMap::new(),
            evidence_base: HashMap::new(),
            world_states: Vec::new(),
        }
    }

    /// Add an agent
    pub fn add_agent(&mut self, agent: String) {
        if !self.agents.contains(&agent) {
            self.agents.push(agent.clone());
            self.justifications.insert(agent, HashMap::new());
        }
    }

    /// Add a justification
    pub fn add_justification(&mut self, agent: &str, proposition: Proposition, term: JustificationTerm) {
        if let Some(agent_justifications) = self.justifications.get_mut(agent) {
            agent_justifications
                .entry(proposition)
                .or_insert_with(Vec::new)
                .push(term.clone());
        }
        
        // Add evidence for the justification term
        let evidence = Evidence {
            term: term.clone(),
            propositions: vec![proposition],
            strength: 1.0,
            source: EvidenceSource::Reasoning,
        };
        
        self.evidence_base.insert(term, evidence);
    }

    /// Check if a proposition is justified
    pub fn is_justified(&self, agent: &str, proposition: &Proposition) -> bool {
        if let Some(agent_justifications) = self.justifications.get(agent) {
            agent_justifications.contains_key(proposition)
        } else {
            false
        }
    }

    /// Get all justifications for a proposition
    pub fn get_justifications(&self, agent: &str, proposition: &Proposition) -> Vec<JustificationTerm> {
        if let Some(agent_justifications) = self.justifications.get(agent) {
            if let Some(terms) = agent_justifications.get(proposition) {
                terms.clone()
            } else {
                Vec::new()
            }
        } else {
            Vec::new()
        }
    }

    /// Combine justifications using the sum operation
    pub fn combine_justifications(&mut self, agent: &str, proposition: &Proposition) -> Option<JustificationTerm> {
        let terms = self.get_justifications(agent, proposition);
        
        if terms.is_empty() {
            return None;
        }
        
        // Start with the first term
        let mut combined = terms[0].clone();
        
        // Combine with the rest using the sum operation
        for i in 1..terms.len() {
            combined = JustificationTerm::Sum(
                Box::new(combined),
                Box::new(terms[i].clone())
            );
        }
        
        Some(combined)
    }

    /// Apply justification logic axioms
    pub fn apply_axioms(&mut self, agent: &str) {
        if let Some(agent_justifications) = self.justifications.get(agent).cloned() {
            // Collect all propositions and their justification terms
            let mut props_and_terms: Vec<(Proposition, JustificationTerm)> = Vec::new();
            
            for (prop, terms) in agent_justifications.iter() {
                for term in terms {
                    props_and_terms.push((prop.clone(), term.clone()));
                }
            }
            
            // Apply axioms
            for (prop1, term1) in &props_and_terms {
                // A3: Positive Introspection - t:φ → !t:(t:φ)
                let introspection_prop = Proposition::Justified(
                    agent.to_string(),
                    term1.clone(),
                    Box::new(prop1.clone())
                );
                
                let introspection_term = JustificationTerm::Factorial(Box::new(term1.clone()));
                
                self.add_justification(agent, introspection_prop, introspection_term);
                
                // Apply A2: Application - t:(φ→ψ) → (s:φ → (t·s):ψ)
                if let Proposition::Implies(p, q) = prop1 {
                    // Find all justifications for p
                    for (prop2, term2) in &props_and_terms {
                        if prop2 == p {
                            // Generate justification for q
                            let application_term = JustificationTerm::Application(
                                Box::new(term1.clone()),
                                Box::new(term2.clone())
                            );
                            
                            self.add_justification(agent, *q.clone(), application_term);
                        }
                    }
                }
            }
        }
    }
    
    /// Add evidence for a justification term
    pub fn add_evidence(&mut self, term: JustificationTerm, evidence: Evidence) {
        self.evidence_base.insert(term, evidence);
    }
    
    /// Get evidence strength for a justification
    pub fn get_evidence_strength(&self, term: &JustificationTerm) -> f64 {
        if let Some(evidence) = self.evidence_base.get(term) {
            evidence.strength
        } else {
            0.0
        }
    }
    
    /// Evaluate justification in a world
    pub fn evaluate_justification(&self, world_id: &str, agent: &str, prop: &Proposition) -> bool {
        // Check if the proposition is in the agent's justification base
        if !self.is_justified(agent, prop) {
            return false;
        }
        
        // Check if the proposition is true in the world
        let world = match self.world_states.iter().find(|w| w.id == world_id) {
            Some(w) => w,
            None => return false,
        };
        
        match prop {
            Proposition::Atomic(p) => *world.propositions.get(p).unwrap_or(&false),
            _ => false, // Simplified: would need recursive evaluation for complex propositions
        }
    }
}
```

## 5. Application Examples

### 5.1 Scientific Method

The scientific method provides a structured approach to justification:

1. **Observation**: Empirical data collection
2. **Hypothesis Formation**: Theoretical explanation
3. **Prediction**: Deductive consequences
4. **Testing**: Experimental verification
5. **Revision**: Modification based on evidence

**Example: Gravitational Theory Justification**:

```rust
// Simplified example of scientific justification
let mut science_system = JustificationSystem::new();
science_system.add_agent("Scientist".to_string());

// Observations
let observation = Proposition::Atomic("Objects fall to Earth".to_string());
let obs_term = JustificationTerm::Constant("Empirical Observation".to_string());
science_system.add_justification("Scientist", observation, obs_term);

// Theory
let theory = Proposition::Atomic("Gravity exists".to_string());
let theory_term = JustificationTerm::Constant("Theoretical Inference".to_string());
science_system.add_justification("Scientist", theory, theory_term);

// Prediction
let prediction = Proposition::Atomic("Objects will fall at calculated rate".to_string());
let pred_term = JustificationTerm::Constant("Theoretical Prediction".to_string());
science_system.add_justification("Scientist", prediction, pred_term);

// Experiment confirms prediction
let experiment = Proposition::Atomic("Objects fall at 9.8 m/s²".to_string());
let exp_term = JustificationTerm::Constant("Experimental Verification".to_string());
science_system.add_justification("Scientist", experiment, exp_term);

// Combined justification of theory
let combined_term = science_system.combine_justifications("Scientist", &theory);
```

### 5.2 Legal Reasoning

Legal reasoning relies on different types of justification:

1. **Statutory Law**: Based on written legislation
2. **Case Law**: Based on precedents
3. **Expert Testimony**: Based on expert opinions
4. **Evidence**: Based on factual data

**Example: Legal Case Justification**:

```rust
// Simplified example of legal justification
let mut legal_system = JustificationSystem::new();
legal_system.add_agent("Judge".to_string());

// Statutory law
let statute = Proposition::Atomic("Law prohibits action A".to_string());
let statute_term = JustificationTerm::Constant("Legal Code Section 123".to_string());
legal_system.add_justification("Judge", statute, statute_term);

// Case precedent
let precedent = Proposition::Atomic("Similar case ruled illegal".to_string());
let precedent_term = JustificationTerm::Constant("Case Smith v. Jones".to_string());
legal_system.add_justification("Judge", precedent, precedent_term);

// Evidence
let evidence = Proposition::Atomic("Defendant performed action A".to_string());
let evidence_term = JustificationTerm::Constant("Witness Testimony".to_string());
legal_system.add_justification("Judge", evidence, evidence_term);

// Verdict
let verdict = Proposition::Atomic("Defendant is guilty".to_string());
let verdict_term = JustificationTerm::Application(
    Box::new(JustificationTerm::Sum(
        Box::new(statute_term),
        Box::new(precedent_term)
    )),
    Box::new(evidence_term)
);
legal_system.add_justification("Judge", verdict, verdict_term);
```

### 5.3 AI Expert Systems

AI expert systems use justification frameworks to explain reasoning:

```rust
// Simplified expert system with justification capabilities
struct ExpertSystem {
    knowledge_base: HashMap<String, bool>,
    rule_base: Vec<(String, String, String)>, // (condition, conclusion, justification)
    justification_system: JustificationSystem,
}

impl ExpertSystem {
    fn new() -> Self {
        let mut system = Self {
            knowledge_base: HashMap::new(),
            rule_base: Vec::new(),
            justification_system: JustificationSystem::new(),
        };
        
        system.justification_system.add_agent("Expert System".to_string());
        system
    }
    
    fn add_fact(&mut self, fact: &str, value: bool) {
        self.knowledge_base.insert(fact.to_string(), value);
        
        if value {
            let prop = Proposition::Atomic(fact.to_string());
            let term = JustificationTerm::Constant("Direct Knowledge".to_string());
            self.justification_system.add_justification("Expert System", prop, term);
        }
    }
    
    fn add_rule(&mut self, condition: &str, conclusion: &str, justification: &str) {
        self.rule_base.push((condition.to_string(), conclusion.to_string(), justification.to_string()));
    }
    
    fn infer(&mut self) -> Vec<(String, String)> {
        let mut new_facts = Vec::new();
        
        for (condition, conclusion, justification) in &self.rule_base {
            // Check if condition is satisfied
            if let Some(true) = self.knowledge_base.get(condition) {
                // Add new conclusion if it's not already known
                if !self.knowledge_base.contains_key(conclusion) {
                    self.knowledge_base.insert(conclusion.clone(), true);
                    
                    // Add justification
                    let condition_prop = Proposition::Atomic(condition.clone());
                    let condition_term = match self.justification_system.get_justifications("Expert System", &condition_prop).first() {
                        Some(term) => term.clone(),
                        None => JustificationTerm::Constant("Assumed".to_string()),
                    };
                    
                    let rule_term = JustificationTerm::Constant(justification.clone());
                    let conclusion_prop = Proposition::Atomic(conclusion.clone());
                    
                    let inference_term = JustificationTerm::Application(
                        Box::new(rule_term),
                        Box::new(condition_term)
                    );
                    
                    self.justification_system.add_justification("Expert System", conclusion_prop, inference_term);
                    
                    new_facts.push((conclusion.clone(), justification.clone()));
                }
            }
        }
        
        new_facts
    }
    
    fn explain(&self, fact: &str) -> Option<Vec<String>> {
        if !self.knowledge_base.contains_key(fact) {
            return None;
        }
        
        let prop = Proposition::Atomic(fact.to_string());
        let terms = self.justification_system.get_justifications("Expert System", &prop);
        
        let mut explanations = Vec::new();
        for term in terms {
            match term {
                JustificationTerm::Constant(reason) => explanations.push(reason),
                JustificationTerm::Application(rule, condition) => {
                    if let JustificationTerm::Constant(rule_name) = *rule {
                        explanations.push(format!("Derived using rule: {}", rule_name));
                    }
                },
                _ => explanations.push("Complex justification".to_string()),
            }
        }
        
        Some(explanations)
    }
}
```

## 6. Related Theories

- **Knowledge Theory**: Explores how justification contributes to knowledge
- **Belief Theory**: Studies the formation and structure of beliefs that require justification
- **Truth Theory**: Investigates the relationship between justification and truth
- **Epistemological Regress Problem**: Addresses the problem of infinite regress in justification
- **Epistemic Coherentism vs. Foundationalism**: Competing theories of justification structure

## 7. References

1. Artemov, S. N. (2001). Explicit Provability and Constructive Semantics. *Bulletin of Symbolic Logic*, 7(1), 1-36.
2. BonJour, L. (1985). *The Structure of Empirical Knowledge*. Harvard University Press.
3. Chisholm, R. M. (1982). *The Foundations of Knowing*. University of Minnesota Press.
4. Goldman, A. I. (1979). What is Justified Belief? In G. S. Pappas (Ed.), *Justification and Knowledge* (pp. 1-23). D. Reidel.
5. Pollock, J. L., & Cruz, J. (1999). *Contemporary Theories of Knowledge*. Rowman & Littlefield.
